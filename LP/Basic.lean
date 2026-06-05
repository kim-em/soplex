/-
  Compatibility re-export of the verified-solve drivers and direct
  FFI wrappers.

  `LP.solveVerifiedWith` (backend-pluggable, `IO`-typed) comes
  from `LPTactic.Basic`; `LP.solveVerified` (FFI-specialised,
  `Except`-typed) comes from `LPBackendSoplexFFI`. `SoplexFFI.Basic`
  is re-exported for the test suite's direct `LP.solveExact`,
  `LP.solveFloat`, `LP.readMps`, `LP.readLp` calls.

  All declarations remain in `namespace LP`, so consumers writing
  `LP.solveVerified`, `LP.solveExact`, etc. keep working
  unchanged.
-/
module

public import LPTactic.Basic
public import LPBackendSoplexFFI
public import SoplexFFI.Basic

@[expose] public section
