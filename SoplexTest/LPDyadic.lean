import Soplex

/-!
`by lp` / `maximize` over `Dyadic` (ordered commutative ring, no inverses).
Coefficients render as native `Dyadic.ofInt`/`ofIntWithPrec` literals (`Eq.refl`
leaves); integer/power-of-two coefficients only (no division).
-/

-- Atomic optimal.
example (a b : Dyadic) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Dyadic) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a ≤ 5 := by lp

-- Strict goal.
example (a b : Dyadic) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a < 6 := by lp

-- Equality goal.
example (a b : Dyadic) (_h₁ : a + b ≤ 3) (_h₂ : 3 ≤ a + b) : a + b = 3 := by lp

-- Cleared multiplier (L = 2).
example (x : Dyadic) (_h : 2 * x ≤ 6) : x ≤ 3 := by lp

-- Infeasible hypotheses: any (comparison) goal follows by Farkas.
example (a : Dyadic) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : a ≤ 0 := by lp

-- Existential (integer witnesses).
example : ∃ x : Dyadic, 1 ≤ x ∧ x ≤ 3 := by lp

-- maximize.
example (x : Dyadic) (_h : 2 * x ≤ 6) : True := by
  maximize (x : Dyadic)
  trivial
