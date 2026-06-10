/-
  Top-level entry point for the `LP` meta-package.

  Bundles the verifier, the `lp` tactic, and the SoPlex FFI backend
  under a single `import LP`. The heavy lifting lives in the split
  packages (`lp-core`, `lp-verify`, `lp-tactic`, `soplex-ffi`,
  `lp-backend-soplex-ffi`); this package pins a coherent set and
  re-exports the convenient surface. The backend registry is
  populated as a side effect of importing `LP.Backend.SoplexFFI`,
  which runs its `initialize` block at module-load time.
-/
module

public import LP.Basic
public meta import LP.Tactic.LP
public import LP.Backend.SoplexFFI

@[expose] public section
