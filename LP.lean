/-
  Top-level entry point for the `LP` library.

  Bundles the verifier, the `lp` tactic, and the SoPlex FFI backend
  under a single `import LP` so existing callers see no change.
  The backend registry (defined in `LP.Core`) is populated as a
  side effect of importing `LP.Backend.SoplexFFI`, which runs its
  `initialize` block at module-load time.

  Tracked migration: this repo will eventually be split into
  `lp-core`, `lp-verify`, `lp-tactic`, and per-backend packages; see
  https://github.com/leanprover/lp/issues/50 for the design. Until
  then this meta-import is the seam.
-/
module

public import LP.Basic
public meta import LP.Tactic.LP
public import LP.Backend.SoplexFFI

@[expose] public section
