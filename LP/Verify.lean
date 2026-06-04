/-
  Pure-Lean certificate checker for SoPlex's exact-mode LP output.

  This module contains the verifier-facing API and is pure Lean
  logically: it performs no `IO` and treats SoPlex as an oracle whose
  certificates must be checked before proofs are produced. In the
  current package layout it is still built through the main `LP`
  dependency graph, which includes the native FFI package. There is no
  separate verifier-only Lake target yet.

  Re-exports:

  * `LP.Verify.Types`     — `Problem`, `Options`, `DualBundle`,
                                    `Certificate`, `Solution`, errors.
  * `LP.Verify.Validate`  — `validate`, `validateOptions`.
  * `LP.Verify.Bool`      — decidable `is*` / `check*` checks.
  * `LP.Verify.Budget`    — `certificateWithinBudget`: ceiling
                                    on rational coordinate bit lengths.
  * `LP.Verify.Arith`     — Rat / Array toolkit and Bool-to-Prop
                                    lemmas used by the soundness layer.
  * `LP.Verify.Prop`      — mathematical `IsFeasible` etc.
  * `LP.Verify.Sound`     — soundness theorems for accepted
                                    certificates.
  * `LP.Verify.Driver`    — `Verified` / `VerifiedSolve`
                                    types and the pure
                                    `Solution`→`Verified` mapping
                                    `verifyOutcome`.

  SoPlex is treated as an oracle; accepted certificates are checked
  here before producing proofs.
-/
module

public import LP.Verify.Types
public import LP.Verify.Validate
public import LP.Verify.Bool
public import LP.Verify.Budget
public import LP.Verify.Arith
public import LP.Verify.Prop
public import LP.Verify.Sound
public import LP.Verify.Driver

@[expose] public section
