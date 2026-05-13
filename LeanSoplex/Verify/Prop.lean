/-
  Mathematical (Prop-level) LP predicates.

  These are stated in minimisation form. The sense-aware wrappers
  `IsOptimal` and `IsUnbounded` defer to the min-canonical versions
  after negating the objective.

  Every `Prop` here is decidable in principle — they're all built out
  of decidable predicates on `Rat` — but we keep the `Bool` view
  separate (`LeanSoplex.Verify.Bool`) to make sure the checker uses
  the computational definition while soundness theorems reason about
  the mathematical one.
-/

import LeanSoplex.Verify.Types
import LeanSoplex.Verify.Bool

namespace LeanSoplex.Verify

open LeanSoplex

/-! ## Canonicalisation. -/

/-- Flip the objective in place. Identity on everything else. -/
def negateObjective (p : Problem) : Problem :=
  { p with c := p.c.map Neg.neg, objOffset := -p.objOffset }

/-- Reduce to minimisation form. -/
def canonicalize (sense : ObjSense) (p : Problem) : Problem :=
  match sense with
  | .minimize => p
  | .maximize => negateObjective p

/-! ## Predicates. -/

/-- `x` satisfies all column bounds of `p`. -/
def ColBoundsSatisfied (p : Problem) (x : Array Rat) : Prop :=
  x.size = p.numVars ∧
  ∀ j : Fin p.numVars,
    let (lo, hi) := p.colBounds[j.val]!
    (∀ l, lo = some l → l ≤ x[j.val]!) ∧
    (∀ h, hi = some h → x[j.val]! ≤ h)

/-- `Ax` satisfies all row bounds of `p`. -/
def RowBoundsSatisfied (p : Problem) (x : Array Rat) : Prop :=
  let ax := evalAx p x
  ∀ i : Fin p.numConstraints,
    let (lo, hi) := p.rowBounds[i.val]!
    (∀ l, lo = some l → l ≤ ax[i.val]!) ∧
    (∀ h, hi = some h → ax[i.val]! ≤ h)

/-- `x` is primal-feasible for `p`. -/
def IsFeasible (p : Problem) (x : Array Rat) : Prop :=
  ColBoundsSatisfied p x ∧ RowBoundsSatisfied p x

/-- `p` has no feasible point. -/
def IsInfeasible (p : Problem) : Prop :=
  ¬ ∃ x, IsFeasible p x

/-- `x` minimises `c·x + objOffset` over the feasible region. -/
def IsOptimalMin (p : Problem) (x : Array Rat) : Prop :=
  IsFeasible p x ∧
    ∀ y, IsFeasible p y → primalObj p x ≤ primalObj p y

/-- The minimisation problem is unbounded below. -/
def IsUnboundedMin (p : Problem) : Prop :=
  (∃ x, IsFeasible p x) ∧
    ∀ M : Rat, ∃ y, IsFeasible p y ∧ primalObj p y < M

/-! ## Prop-level dual feasibility.

  Mirrors the Bool checks in `LeanSoplex.Verify.Bool` but at the Prop
  level so the soundness proofs can talk about them without
  unfolding `Array.all`/`arrayEq`. Bridges Bool↔Prop live in
  `LeanSoplex.Verify.Arith`. -/

/-- Componentwise nonnegativity plus zero-where-the-matching-bound-is-
    absent. Pulled out so both `IsDualFeasible` and `IsFarkasDualFeasible`
    can reuse it. -/
structure DualNonnegZeroWhereAbsent {m n : Nat}
    (p : Problem) (d : DualBundle m n) : Prop where
  numConstraints_eq : m = p.numConstraints
  numVars_eq       : n = p.numVars
  row_nonneg : ∀ i, i < p.numConstraints →
    0 ≤ d.rowLower.toArray[i]! ∧ 0 ≤ d.rowUpper.toArray[i]!
  col_nonneg : ∀ j, j < p.numVars →
    0 ≤ d.colLower.toArray[j]! ∧ 0 ≤ d.colUpper.toArray[j]!
  row_zero_absent : ∀ i, i < p.numConstraints →
    ((p.rowBounds[i]!).1 = none → d.rowLower.toArray[i]! = 0) ∧
    ((p.rowBounds[i]!).2 = none → d.rowUpper.toArray[i]! = 0)
  col_zero_absent : ∀ j, j < p.numVars →
    ((p.colBounds[j]!).1 = none → d.colLower.toArray[j]! = 0) ∧
    ((p.colBounds[j]!).2 = none → d.colUpper.toArray[j]! = 0)

namespace DualNonnegZeroWhereAbsent

variable {m n : Nat} {p : Problem} {d : DualBundle m n}

/-- Legacy convenience: `d.rowLower.toArray.size = p.numConstraints`.
    Was a structure field in the pre-`Vector` design; kept as a
    derived accessor so existing dot-notation proofs (e.g.
    `hDual.rowLower_size`) still work. -/
theorem rowLower_size (h : DualNonnegZeroWhereAbsent p d) :
    d.rowLower.toArray.size = p.numConstraints := by
  rw [Vector.size_toArray]; exact h.numConstraints_eq

theorem rowUpper_size (h : DualNonnegZeroWhereAbsent p d) :
    d.rowUpper.toArray.size = p.numConstraints := by
  rw [Vector.size_toArray]; exact h.numConstraints_eq

theorem colLower_size (h : DualNonnegZeroWhereAbsent p d) :
    d.colLower.toArray.size = p.numVars := by
  rw [Vector.size_toArray]; exact h.numVars_eq

theorem colUpper_size (h : DualNonnegZeroWhereAbsent p d) :
    d.colUpper.toArray.size = p.numVars := by
  rw [Vector.size_toArray]; exact h.numVars_eq

end DualNonnegZeroWhereAbsent

/-- Stationarity against an arbitrary `q : Array Rat`:
    `Aᵀ(yL − yU) + (zL − zU) = q` componentwise. -/
def StationarityAgainst {m n : Nat}
    (p : Problem) (d : DualBundle m n) (q : Array Rat) : Prop :=
  ∀ j, j < p.numVars →
    (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))[j]! +
      (d.colLower.toArray[j]! - d.colUpper.toArray[j]!) = q[j]!

/-- Full dual feasibility for the optimality certificate: nonnegativity,
    zero-where-absent, and stationarity against the objective `c`. -/
structure IsDualFeasible {m n : Nat} (p : Problem) (d : DualBundle m n) : Prop where
  nonneg_zero_absent : DualNonnegZeroWhereAbsent p d
  stationarity : StationarityAgainst p d p.c

/-- Farkas (homogeneous) dual feasibility: nonnegativity, zero-where-absent,
    and stationarity against `0`. -/
structure IsFarkasDualFeasible {m n : Nat}
    (p : Problem) (d : DualBundle m n) : Prop where
  nonneg_zero_absent : DualNonnegZeroWhereAbsent p d
  stationarity_zero : ∀ j, j < p.numVars →
    (evalATy p (arraySub d.rowLower.toArray d.rowUpper.toArray))[j]! +
      (d.colLower.toArray[j]! - d.colUpper.toArray[j]!) = 0

/-- Prop form of `isRecessionRay`. Each row/column with a finite bound
    on a given side constrains the ray's sign on the matching `r[j]!`
    or `(evalAx p r)[i]!`. Equality rows / boxed columns collapse to
    `= 0` by antisymmetry. -/
structure IsRecessionRay (p : Problem) (r : Array Rat) : Prop where
  size : r.size = p.numVars
  col_lo_nonneg : ∀ j, j < p.numVars → (p.colBounds[j]!).1.isSome = true → 0 ≤ r[j]!
  col_hi_nonpos : ∀ j, j < p.numVars → (p.colBounds[j]!).2.isSome = true → r[j]! ≤ 0
  row_lo_nonneg : ∀ i, i < p.numConstraints →
    (p.rowBounds[i]!).1.isSome = true → 0 ≤ (evalAx p r)[i]!
  row_hi_nonpos : ∀ i, i < p.numConstraints →
    (p.rowBounds[i]!).2.isSome = true → (evalAx p r)[i]! ≤ 0

/-! ## Sense-aware wrappers. -/

/-- Optimality wrt the user's original sense. -/
def IsOptimal (p : Problem) (sense : ObjSense) (x : Array Rat) : Prop :=
  IsOptimalMin (canonicalize sense p) x

/-- Unboundedness wrt the user's original sense. -/
def IsUnbounded (p : Problem) (sense : ObjSense) : Prop :=
  IsUnboundedMin (canonicalize sense p)

end LeanSoplex.Verify
