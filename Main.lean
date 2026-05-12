/-
  Smoke-test executable for `lean-soplex`.

  Runs the toy LP

      minimise   x + y
      subject to x + y = 1
                 0 ≤ x, 0 ≤ y

  whose optimum is `(x, y) = (0, 1)` (or any convex combination on the
  segment) with objective value `1`. Used by CI to confirm:

  * the FFI links against SoPlex,
  * SoPlex's runtime is loaded successfully,
  * a non-trivial LP solve completes and returns a sane result.

  Exits with status 0 on success; non-zero on any unexpected output.
-/

import LeanSoplex

open LeanSoplex

def main : IO UInt32 := do
  IO.println s!"SoPlex version: {LeanSoplex.version}"

  -- Validate the C++ exception ABI on every platform with a
  -- nontrivial cross-stdlib link to police:
  --
  -- * Windows pairs an explicit `libstdc++.a` with Lean's clang-
  --   auto-linked `libc++.a` and relies on `--allow-multiple-
  --   definition` (see `lakefile.lean`); if libc++ ever wins the
  --   link, the catch will miss and the DLL is broken.
  -- * Linux compiles SoPlex with the system g++ (libstdc++); Lean's
  --   clang would otherwise pull `libc++abi.so.1` into `DT_NEEDED`
  --   and its personality function would win symbol resolution at
  --   runtime, swallowing every libstdc++-style throw. The lakefile
  --   suppresses that with `-nostdlib++`; this check is the canary
  --   for any future regression.
  --
  -- Skipped on macOS because the entire toolchain uses libc++ — there
  -- is no conflict to validate.
  unless System.Platform.isOSX do
    let exnRc := LeanSoplex.exceptionCheck ()
    IO.println s!"exception check = {exnRc}"
    if exnRc ≠ 0 then
      IO.eprintln s!"std::exception throw/catch broken (rc={exnRc}); cross-stdlib ABI mismatch"
      return 3

  let result := smokeSolve
    (c    := #[1.0, 1.0])
    (b    := #[1.0])
    (rows := #[0, 0])
    (cols := #[0, 1])
    (vals := #[1.0, 1.0])

  IO.println s!"ret    = {result.ret}"
  IO.println s!"obj    = {result.obj}"
  IO.println s!"primal = {result.primal.toList}"

  if result.ret ≠ 0 then
    IO.eprintln s!"expected optimal (ret=0), got ret={result.ret}"
    return 1
  -- Objective is `1` up to floating-point slop.
  if (result.obj - 1.0).abs > 1e-9 then
    IO.eprintln s!"expected objective ≈ 1.0, got {result.obj}"
    return 2
  return 0
