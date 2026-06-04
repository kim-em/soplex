import Lake
open System Lake DSL

/-! # `Soplex` build configuration

  The direct SoPlex binding lives in the `SoplexFFI` package.
  This package builds the high-level verified API on top of it.
-/

require LPCore from git "https://github.com/kim-em/lp-core" @
  "66ac782a11ba2f8c2d3b4ad446000cf20b3f39b7"

require LPVerify from git "https://github.com/kim-em/lp-verify" @
  "e11fa03103dea73fa238c86522018a7267b824c2"

require LPTactic from git "https://github.com/kim-em/lp-tactic" @
  "809fd8a09506213e50b6198dd6261166f4d78b54"

require LPBackendSoplexFFI from git
  "https://github.com/kim-em/lp-backend-soplex-ffi" @
  "0c616e7cf92f5fbe1c9897587a9f26925c514798"

require SoplexFFI from git "https://github.com/kim-em/soplex-ffi" @
  "b1cafbcd456cf999c06ab8207e054e9429e9d7bc"

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

package Soplex where
  moreLinkArgs := soplexFFIRuntimeLinkArgs

@[default_target]
lean_lib Soplex where
  roots := #[`Soplex]
  globs := #[`Soplex, `Soplex.Basic, `Soplex.Verify, `Soplex.Verify.+,
             `Soplex.LP.Core, `Soplex.Backend.SoplexFFI]
  precompileModules := true
  -- Keep the native runtime link arguments on the downstream library as
  -- well as the package. `Soplex.Basic` imports and calls the FFI during
  -- elaboration-time probes, so its shared-library link step must resolve
  -- the same platform libraries as the final executables.
  moreLinkArgs := soplexFFIRuntimeLinkArgs
  -- Force the `SoplexFFI` native library to build before any module in
  -- this library. With `precompileModules`, every module's `:dynlib`
  -- link picks up `moreLinkArgs`, which on Windows names the staged
  -- `vendor/mingw-libs/*.a` archives. Those archives are staged as a
  -- side effect of the `SoplexFFI` native build. Pure-Lean modules such
  -- as `Soplex.Tactic.*` import nothing from `SoplexFFI`, so
  -- without this dependency their dynlib link can run first and fail
  -- with `no such file or directory` on the not-yet-staged archives.
  needs := #[BuildKey.packageTarget `SoplexFFI `soplexffi]

/-- Shared scaffolding for the `SoplexTest/` executables. Keeping it as
    a `lean_lib` lets each test exe pick up `SoplexTest.Common` and
    `SoplexTest.SolveCommon` as compiled dependencies. -/
lean_lib SoplexTest where
  roots := #[`SoplexTest.Common, `SoplexTest.SolveCommon]

/-- The `by lp` / `maximize` tactic tests. Building this library elaborates every
    `example := by lp`, exercising the carrier-parametrized tactic end to end
    against the FFI backend — atomic, `∃`, `maximize`, inner-`∀`, Benders, and
    scaling over `Rat`, plus the `Int`/`Dyadic`/`Nat` carrier lanes. -/
lean_lib SoplexLPTest where
  roots := #[`SoplexTest.LP, `SoplexTest.LPExistential, `SoplexTest.LPMaximize,
             `SoplexTest.LPInnerForall, `SoplexTest.LPBenders, `SoplexTest.LPScaling,
             `SoplexTest.LPInt, `SoplexTest.LPDyadic, `SoplexTest.LPNat,
             `SoplexTest.LPReject]

/-- End-to-end FFI runtime check: prints the SoPlex version, runs the
    cross-stdlib ABI throw/catch test, and runs a small LP sanity check.
    Used by CI to confirm the binding links, loads, and computes on every
    platform. -/
lean_exe «ffi-check» where
  root := `SoplexTest.FFICheck

lean_exe «verify-tests» where
  root := `SoplexTest.Verify

lean_exe «solve-exact-tests» where
  root := `SoplexTest.SolveExact

lean_exe «solve-float-tests» where
  root := `SoplexTest.SolveFloat

lean_exe «solve-compare-tests» where
  root := `SoplexTest.SolveCompare

lean_exe «solve-verified-tests» where
  root := `SoplexTest.SolveVerified

lean_exe «accessor-goldens» where
  root := `SoplexTest.AccessorGoldens

lean_exe «file-io-tests» where
  root := `SoplexTest.FileIo

/-- `lake test` driver: builds and runs every test executable. -/
@[test_driver]
lean_exe «test-runner» where
  root := `SoplexTest.Runner

lean_exe «quickstart-example» where
  root := `Examples.Quickstart
