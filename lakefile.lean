import Lake
open System Lake DSL

/-! # `LP` build configuration

  The direct SoPlex binding lives in the `SoplexFFI` package.
  This package builds the high-level verified API on top of it.
-/

require LPCore from git "https://github.com/leanprover/lp-core" @
  "70ca150585f8439a830374b5bec602d391addbc9"

require LPVerify from git "https://github.com/leanprover/lp-verify" @
  "e8e337f4b6c6f666b5dc7b43bc1ae6cc9d15fa05"

require LPTactic from git "https://github.com/leanprover/lp-tactic" @
  "7ea556ad4d2bbd8d9d3e790cfb05206bd7f24d91"

require LPBackendSoplexFFI from git
  "https://github.com/leanprover/lp-backend-soplex-ffi" @
  "314c61386a376443d0450cef834a340c3a5564c9"

require SoplexFFI from git "https://github.com/leanprover/soplex-ffi" @
  "0849137dd4d7ad68edb9c616a6e9f9a7625be529"

def sanitizerEnabled : Bool :=
  match get_config? sanitize with
  | some s => s != "0" && s != "false"
  | none => false

def sanitizerArgs : Array String :=
  if sanitizerEnabled then
    #["-fsanitize=address", "-fsanitize=undefined",
      "-fno-sanitize=vptr,function",
      "-fno-omit-frame-pointer", "-g"]
  else
    #[]

def soplexFFIRoot : FilePath := __dir__ / defaultPackagesDir / "SoplexFFI"

/-- The Lean toolchain's own `lib` directory, passed by CI as `-KleanLibDir=...`
    (`$(lean --print-prefix)/lib`). Used only by the sanitizer lane (below) to put
    the toolchain libc++ ahead of the `-L/usr/lib*` dirs that lane also needs. -/
def leanLibDirArgs : Array String :=
  match get_config? leanLibDir with
  | some d => #[s!"-L{d}"]
  | none => #[]

def soplexFFIRuntimeLinkArgs : Array String :=
  if System.Platform.isOSX then
    #[]
  else if System.Platform.isWindows then
    let mingwLibDir := soplexFFIRoot / "vendor" / "mingw-libs"
    #["-Wl,--allow-multiple-definition",
      (mingwLibDir / "libstdc++.a").toString,
      (mingwLibDir / "libgmpxx.a").toString,
      (mingwLibDir / "libgmp.a").toString,
      s!"-L{mingwLibDir}",
      "-lgcc_s",
      "-lmingwex",
      "-lmsvcrt"]
  else if sanitizerEnabled then
    -- Sanitizer lane: the ASan runtime link needs `-lresolv` etc. from the
    -- `-L/usr/lib*` dirs, but those dirs also hold Ubuntu's `libc++.so` and would
    -- shadow the toolchain libc++ for `-lc++` (same failure as the default lane).
    -- So put the toolchain `lib` dir (`-KleanLibDir`, set by CI) FIRST, ahead of
    -- `/usr/lib*`, so `-lc++` still binds to the toolchain's libc++.
    leanLibDirArgs ++
    #["-L/usr/lib/x86_64-linux-gnu",
      "-L/usr/lib/aarch64-linux-gnu",
      "-L/usr/lib64",
      "-L/usr/lib"] ++ sanitizerArgs
  else
    -- Default Linux lane: do NOT add `-L/usr/lib/x86_64-linux-gnu` (etc.). Those
    -- dirs hold Ubuntu's `libc++.so`, and a command-line `-L` is searched *before*
    -- the toolchain's own lib dir, so they shadow the Lean toolchain's libc++ for
    -- `-lc++`. Ubuntu's libc++ 18 does not export the C++20 symbols
    -- (`std::__1::__hash_memory`, `__atomic_wait_native`) that the toolchain-built
    -- `libleanrt.a`/`libleancpp.a` reference (the toolchain's own libc++ does), so
    -- the shadow caused "undefined symbol" link failures with `precompileModules`
    -- on v4.31. GMP/Boost resolve via the toolchain clang's default search dirs.
    #[]

package LP where
  moreLinkArgs := soplexFFIRuntimeLinkArgs

@[default_target]
lean_lib LP where
  roots := #[`LP]
  globs := #[`LP, `LP.Basic, `LP.Verify, `LP.Verify.+,
             `LP.Core, `LP.Backend.SoplexFFI]
  precompileModules := true
  -- Keep the native runtime link arguments on the downstream library as
  -- well as the package. `LP.Basic` imports and calls the FFI during
  -- elaboration-time probes, so its shared-library link step must resolve
  -- the same platform libraries as the final executables.
  moreLinkArgs := soplexFFIRuntimeLinkArgs
  -- Force the `SoplexFFI` native library to build before any module in
  -- this library. With `precompileModules`, every module's `:dynlib`
  -- link picks up `moreLinkArgs`, which on Windows names the staged
  -- `vendor/mingw-libs/*.a` archives. Those archives are staged as a
  -- side effect of the `SoplexFFI` native build. Pure-Lean modules such
  -- as `LP.Tactic.*` import nothing from `SoplexFFI`, so
  -- without this dependency their dynlib link can run first and fail
  -- with `no such file or directory` on the not-yet-staged archives.
  needs := #[BuildKey.packageTarget `SoplexFFI `soplexffi]

/-- Shared scaffolding for the `LPTest/` executables. Keeping it as
    a `lean_lib` lets each test exe pick up `LPTest.Common` and
    `LPTest.SolveCommon` as compiled dependencies. -/
lean_lib LPTest where
  roots := #[`LPTest.Common, `LPTest.SolveCommon]

/-- The `by lp` / `maximize` tactic tests. Building this library elaborates every
    `example := by lp`, exercising the carrier-parametrized tactic end to end
    against the FFI backend — atomic, `∃`, `maximize`, inner-`∀`, Benders, and
    scaling over `Rat`, plus the `Int`/`Dyadic`/`Nat` carrier lanes. -/
lean_lib LPTacticTest where
  roots := #[`LPTest.LP, `LPTest.LPExistential, `LPTest.LPMaximize,
             `LPTest.LPInnerForall, `LPTest.LPBenders, `LPTest.LPScaling,
             `LPTest.LPInt, `LPTest.LPDyadic, `LPTest.LPNat,
             `LPTest.LPReject]

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and runs a small LP sanity check.
    Used by CI to confirm the binding links, loads, and computes on every
    platform. -/
lean_exe «ffi-check» where
  root := `LPTest.FFICheck

lean_exe «verify-tests» where
  root := `LPTest.Verify

lean_exe «solve-exact-tests» where
  root := `LPTest.SolveExact

lean_exe «solve-float-tests» where
  root := `LPTest.SolveFloat

lean_exe «solve-compare-tests» where
  root := `LPTest.SolveCompare

lean_exe «solve-verified-tests» where
  root := `LPTest.SolveVerified

lean_exe «accessor-goldens» where
  root := `LPTest.AccessorGoldens

lean_exe «file-io-tests» where
  root := `LPTest.FileIo

/-- `lake test` driver: builds and runs every test executable. -/
@[test_driver]
lean_exe «test-runner» where
  root := `LPTest.Runner

lean_exe «quickstart-example» where
  root := `Examples.Quickstart
