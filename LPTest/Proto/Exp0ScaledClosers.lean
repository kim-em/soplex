/-
Exp 0 — SCALED closers for a generic ordered `IntModule`.

De-risks the #1 soundness gap from the plan: integerizing soplex's rational
Farkas multipliers forces scaling the GOAL by a positive integer `L`, so the
closing identity is `L • (rhs - lhs) + s = C`, not the unscaled `rhs - lhs + s
= C` that lp's current `direct_le_close` expects. The hard part is the BACKWARD
cancellation `0 ≤ L • z → 0 ≤ z` (for `0 < L`), which `zsmul_nonpos` (forward
only) does not give — it needs `IsLinearOrder` + a contradiction via
`zsmul_neg_iff`.

This file proves the generic backward lemmas and the four scaled closers, then
instantiates them at `Rat`. No soplex, no Mathlib — only Lean core `Grind`.

Success = this file typechecks (and the `Rat` examples elaborate, confirming the
core `Rat` grind instances resolve).
-/
import Init.Grind.Ordered.Module
import Init.Grind.Ordered.Rat

namespace Exp0

open Std
open Lean.Grind
open Lean.Grind.OrderedAdd

variable {M : Type u}
  [IntModule M] [LE M] [LT M] [IsLinearOrder M]
  [LawfulOrderLT M] [OrderedAdd M]

/-- Backward cancellation of a positive integer scalar from a nonneg product. -/
theorem nonneg_of_zsmul_nonneg {L : Int} {z : M} (hL : 0 < L) (h : 0 ≤ L • z) :
    0 ≤ z := by
  apply Classical.byContradiction
  intro hz
  have hz' : z < 0 := LinearOrder.lt_of_not_le hz
  have hneg : L • z < 0 := (OrderedAdd.zsmul_neg_iff L hz').mpr hL
  exact Preorder.lt_irrefl 0 (Preorder.lt_of_le_of_lt h hneg)

/-- Backward cancellation of a positive integer scalar from a positive product. -/
theorem pos_of_zsmul_pos {L : Int} {z : M} (hL : 0 < L) (h : 0 < L • z) :
    0 < z := by
  apply Classical.byContradiction
  intro hz
  have hz' : z ≤ 0 := LinearOrder.le_of_not_lt hz
  have hnp : L • z ≤ 0 := OrderedAdd.zsmul_nonpos (Preorder.le_of_lt hL) hz'
  exact Preorder.lt_irrefl 0 (Preorder.lt_of_lt_of_le h hnp)

/-- Scaled `≤` closer: from a positive scale `L`, a nonpositive row-sum `s`, a
nonnegative residual `C`, and the scaled identity, conclude `lhs ≤ rhs`. -/
theorem scaled_le_close {L : Int} {lhs rhs s C : M}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 ≤ C)
    (hIdent : L • (rhs - lhs) + s = C) : lhs ≤ rhs := by
  apply sub_nonneg_iff.mp
  apply nonneg_of_zsmul_nonneg hL
  have hstep : L • (rhs - lhs) = C - s := by
    rw [← hIdent, AddCommGroup.add_sub_cancel]
  rw [hstep]
  exact sub_nonneg_iff.mpr (le_trans hSum hC)

/-- Scaled strict closer. -/
theorem scaled_lt_close {L : Int} {lhs rhs s C : M}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 < C)
    (hIdent : L • (rhs - lhs) + s = C) : lhs < rhs := by
  apply sub_pos_iff.mp
  apply pos_of_zsmul_pos hL
  have hstep : L • (rhs - lhs) = C - s := by
    rw [← hIdent, AddCommGroup.add_sub_cancel]
  rw [hstep]
  exact sub_pos_iff.mpr (Preorder.lt_of_le_of_lt hSum hC)

-- Infeasible closer (no goal to scale): a nonpositive sum equal to a positive
-- constant is contradictory.
omit [OrderedAdd M] in
theorem scaled_infeasible_close {s C : M}
    (hSum : s ≤ 0) (hC : 0 < C) (hIdent : s = C) : False := by
  rw [hIdent] at hSum
  exact Preorder.lt_irrefl 0 (Preorder.lt_of_lt_of_le hC hSum)

/-- Equality closer: two scaled `≤` certificates in opposite directions. -/
theorem scaled_eq_close {L₁ L₂ : Int} {lhs rhs s₁ s₂ C₁ C₂ : M}
    (hL₁ : 0 < L₁) (hSum₁ : s₁ ≤ 0) (hC₁ : 0 ≤ C₁)
    (hId₁ : L₁ • (rhs - lhs) + s₁ = C₁)
    (hL₂ : 0 < L₂) (hSum₂ : s₂ ≤ 0) (hC₂ : 0 ≤ C₂)
    (hId₂ : L₂ • (lhs - rhs) + s₂ = C₂) : lhs = rhs :=
  le_antisymm (scaled_le_close hL₁ hSum₁ hC₁ hId₁)
              (scaled_le_close hL₂ hSum₂ hC₂ hId₂)

/-! ## Instantiation at `Rat`

These confirm the closers elaborate and the core `Rat` grind instances
(`IntModule`/`OrderedAdd`/`IsLinearOrder`/`LawfulOrderLT`) resolve. The scaled
identity hypothesis is left abstract here: discharging a *concrete* `L • (…)`
identity requires evaluating `zsmul` on numeric literals, which is Exp 5's job
(`decide` cannot reduce `•` on `Rat`). -/

example (x y : Rat) {L : Int} {s C : Rat}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 ≤ C)
    (hId : L • (y - x) + s = C) : x ≤ y :=
  scaled_le_close hL hSum hC hId

example (x y : Rat) {L : Int} {s C : Rat}
    (hL : 0 < L) (hSum : s ≤ 0) (hC : 0 < C)
    (hId : L • (y - x) + s = C) : x < y :=
  scaled_lt_close hL hSum hC hId

example {s C : Rat} (hSum : s ≤ 0) (hC : 0 < C) (hId : s = C) : False :=
  scaled_infeasible_close hSum hC hId

example (x y : Rat) {L₁ L₂ : Int} {s₁ s₂ C₁ C₂ : Rat}
    (hL₁ : 0 < L₁) (hSum₁ : s₁ ≤ 0) (hC₁ : 0 ≤ C₁) (hId₁ : L₁ • (y - x) + s₁ = C₁)
    (hL₂ : 0 < L₂) (hSum₂ : s₂ ≤ 0) (hC₂ : 0 ≤ C₂) (hId₂ : L₂ • (x - y) + s₂ = C₂) :
    x = y :=
  scaled_eq_close hL₁ hSum₁ hC₁ hId₁ hL₂ hSum₂ hC₂ hId₂

end Exp0
