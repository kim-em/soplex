/-
Exp 1 — input-row denominator clearing.

De-risks the #2/#3 gaps from the plan (per the Codex review):
  * Integer multipliers keep residual *products* integral only if the input rows
    are already integer-affine. Section A confirms an integer-affine row is
    scalable entirely within `IntModule` (no ring/field needed).
  * Rational input coefficients (`(1/2)·x ≤ 3`) cannot even be stated over a bare
    `IntModule` (no `*` on `M`, no `1/2 : M`); clearing them to integer-affine
    form requires a *field*. Section B confirms the clearing goes through over an
    ordered field and pins the field dependency.

Conclusion this retires: pure-IntModule `lp` covers integer-affine syntax;
rational-affine input must escalate `α` to an ordered field for the clearing step.
No soplex, no Mathlib — only Lean core `Grind`.
-/
import Init.Grind.Ordered.Module
import Init.Grind.Ordered.Field
import Init.Grind.Ordered.Rat
import Init.GrindInstances.Ring.Rat

namespace Exp1

open Std
open Lean.Grind

/-! ## Section A — integer-affine rows scale within a bare `IntModule` -/

section IntAffine
open Lean.Grind.IntModule Lean.Grind.OrderedAdd
variable {M : Type u}
  [IntModule M] [LE M] [LT M] [IsLinearOrder M] [LawfulOrderLT M] [OrderedAdd M]

-- An integer-affine row `≤ 0`, scaled by a nonnegative integer, stays `≤ 0`.
omit [LT M] [LawfulOrderLT M] in
theorem clear_int_row {k : Int} {row : M} (hk : 0 ≤ k) (h : row ≤ 0) : k • row ≤ 0 :=
  OrderedAdd.zsmul_nonpos hk h

/-- Scaling distributes over an integer-affine combination — pure `IntModule`
algebra (`zsmul_add` + `mul_zsmul`), no ring/field structure used. -/
example (k a b : Int) (x y : M) :
    k • (a • x + b • y) = (k * a) • x + (k * b) • y := by
  rw [zsmul_add, ← mul_zsmul, ← mul_zsmul]

end IntAffine

-- `Rat` is an `IntModule`; an integer-affine row clears with no field structure.
example (x : Rat) (h : (3 : Int) • x ≤ 0) : (6 : Int) • x ≤ 0 := by
  have := clear_int_row (k := 2) (by decide) h
  rwa [← IntModule.mul_zsmul] at this

/-! ## Section B — rational coefficients require a field to clear -/

section RatAffine
open Lean.Grind.OrderedRing
variable {K : Type u}
  [Field K] [LE K] [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K]

/-- Clear a rational coefficient `c` by multiplying through by a positive `d`
with `d * c = 1`. This is a *field/ring* fact (`mul_le_mul_of_nonneg_left`,
`mul_assoc`, `one_mul`) — there is no `IntModule`-only proof. -/
theorem clear_field_row {d c x b : K} (hd : 0 < d) (hdc : d * c = 1)
    (h : c * x ≤ b) : x ≤ d * b := by
  have hstep := OrderedRing.mul_le_mul_of_nonneg_left h (Preorder.le_of_lt hd)
  rwa [← Semiring.mul_assoc, hdc, Semiring.one_mul] at hstep

end RatAffine

-- At `Rat` (a field): `(1/2)·x ≤ 3` clears to `x ≤ 2·3` by multiplying by `2`.
-- (`native_decide` for the closed field identity `2 * (1/2) = 1`: `decide` cannot
-- reduce `Rat` multiplication/division of literals — the same literal-arithmetic
-- gap Exp 5 must close generically via constructive proof terms.)
example (x : Rat) (h : (1 / 2 : Rat) * x ≤ 3) : x ≤ 2 * 3 :=
  clear_field_row (by decide) (by native_decide) h

/-
Scope check (the failure half of the experiment): over a bare `IntModule` the
rational-coefficient row cannot even be *stated* — `M` has no `*` and no `1/2 : M`.
Uncommenting the next line fails to elaborate, which is the point:

  example {M : Type u} [IntModule M] (x : M) (h : (1 / 2 : M) * x ≤ 0) : True := trivial

So decision 5 holds: integer-affine ⇒ IntModule; rational-affine ⇒ field.
-/

end Exp1
