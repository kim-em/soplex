/-
  Compatibility import for shared solver data types.

  The definitions live in `LPCore.Types` (the new `leanprover/lp-core`
  package) so the FFI binding, the verifier, and every future
  backend agree on the same `Problem`, `Solution`, and certificate
  structures without anyone depending on the FFI build.
-/
module

public import LPCore.Types

@[expose] public section
