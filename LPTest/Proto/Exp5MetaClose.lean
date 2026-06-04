/-
Exp 5 — generic meta construction of the residual-sign discharge.

Today lp closes `0 ≤ c` with `mkDecideProof` over a closed `Rat` (and we saw in
Exp 0/1 that `decide` cannot even reduce `•`/`*` on `Rat`). Over an abstract
carrier `α` there is no `decide`. This experiment confirms the constructive
replacement: given an `Expr` for `α` and a nonnegative integer `n`, build the
`α`-literal `(n : α)` and a proof of `0 ≤ (n : α)` via
`Lean.Grind.OrderedRing.ofNat_nonneg`, entirely at meta time — then `check` the
term and infer its type. Demonstrated at `Rat`; the same `mkAppOptM` works for
any `α` carrying the grind instances (Exp 3 confirmed `ℝ` has them).

Also a microbenchmark: building many such proofs, as a first read on the
"generic construction vs cached `Rat`" cost (open risk).

Run:  cd /Users/kim/projects/lean/lean-soplex && lake env lean SoplexTest/Proto/Exp5MetaClose.lean
-/
import Lean
import Init.Grind.Ordered.Rat

open Lean Meta

namespace Exp5

/-- Build the `α`-literal `(OfNat.ofNat n : α)`. -/
def mkOfNatLit (α : Expr) (n : Nat) : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some α, some (mkNatLit n), none]

/-- Build a proof of `0 ≤ (OfNat.ofNat n : α)` via `OrderedRing.ofNat_nonneg`.
Binders: `{R} [Ring][LE][LT][LawfulOrderLT][IsPreorder][OrderedRing] (x : Nat)`. -/
def mkNonnegProof (α : Expr) (n : Nat) : MetaM Expr :=
  mkAppOptM ``Lean.Grind.OrderedRing.ofNat_nonneg
    #[some α, none, none, none, none, none, none, some (mkNatLit n)]

/-- The generic sign-discharge: literal + its nonneg proof, type-checked. -/
def buildNonneg (α : Expr) (n : Nat) : MetaM (Expr × Expr) := do
  let lit ← mkOfNatLit α n
  let pf ← mkNonnegProof α n
  check lit
  check pf
  return (lit, ← inferType pf)
end Exp5

open Exp5

-- At `Rat`: build `(7 : Rat)` and a checked proof of `0 ≤ (7 : Rat)`.
run_meta do
  let (lit, ty) ← buildNonneg (mkConst ``Rat) 7
  logInfo m!"literal: {lit}"
  logInfo m!"nonneg proof type: {ty}"

-- Microbenchmark: build + check 2000 literal/nonneg proofs at `Rat`.
run_meta do
  let α := mkConst ``Rat
  let t0 ← IO.monoMsNow
  for i in [0:2000] do
    let _ ← buildNonneg α (i % 97)
  let t1 ← IO.monoMsNow
  logInfo m!"built+checked 2000 nonneg proofs in {t1 - t0} ms"
