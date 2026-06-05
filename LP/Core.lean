/-
  Compatibility re-export of the `LPBackend` record (from
  `leanprover/lp-core`) and the process-global registry (from
  `leanprover/lp-tactic`).

  Pre-split, this module owned both the record definition and the
  registry. Per the issue #50 non-goal "global registry state lives
  in the tactic layer", the registry now lives in `LPTactic.Registry`
  while the abstract record stays in `LPCore.Backend`. Both are
  re-exported here so any consumer writing
  `LP.LPBackend` / `LP.registerBackend` /
  `LP.resolveBackend` / `LP.availableBackends` keeps
  working unchanged.
-/
module

public import LPCore.Backend
public import LPTactic.Registry

@[expose] public section
