/-
  Compatibility re-export of `LPBackendSoplexFFI.Adapter`
  (`leanprover/lp-backend-soplex-ffi`).

  The adapter self-registers on import — anyone writing
  `import LP` (which transitively imports this module) gets the
  `"soplex-ffi"` backend installed in the registry at priority 10.
-/
module

public import LPBackendSoplexFFI.Adapter

@[expose] public section
