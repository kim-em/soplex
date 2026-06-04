import LP

/-!
`by lp` / `maximize` over `Int` (ordered commutative ring). The ℚ-Farkas
certificate is reconstructed with native `Int` literals (`Eq.refl` leaves) and
integer-cleared multipliers; no integrality/cut reasoning (that is `omega`/
`cutsat`'s job) — only ℚ-valid implications.
-/

-- Atomic optimal (two-row certificate).
example (a b : Int) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Int) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a ≤ 5 := by lp

-- Strict goal (strict Farkas residual).
example (a b : Int) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a - b ≤ 1) : 3 * a < 6 := by lp

-- Equality goal (antisymmetry from two ≤ certificates).
example (a b : Int) (_h₁ : a + b ≤ 3) (_h₂ : 3 ≤ a + b) : a + b = 3 := by lp

-- Fractional multiplier cleared to integers (L = 2).
example (x : Int) (_h : 2 * x ≤ 6) : x ≤ 3 := by lp

-- Infeasible hypotheses: any (comparison) goal follows by Farkas.
example (a : Int) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : a ≤ 0 := by lp

-- Existential: integer witness (box vertex is integral).
example : ∃ x : Int, 3 ≤ x ∧ x ≤ 5 := by lp
example : ∃ x y : Int, 2 ≤ x ∧ 1 ≤ y ∧ x + y ≤ 4 := by lp

-- Existential contradiction path: inconsistent outer hyps, infeasible body.
example (a : Int) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : ∃ y : Int, 1 ≤ y ∧ y ≤ 0 := by lp

-- maximize: integral optimum.
example (x : Int) (_h : 2 * x ≤ 6) : True := by
  maximize (x : Int)
  trivial

-- Inconsistent hypotheses also close a bare `False` goal (carrier from hyps).
example (a : Int) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : False := by lp
example (x y : Int) (_h₁ : x + y ≤ 1) (_h₂ : 2 ≤ x) (_h₃ : 1 ≤ y) : False := by lp
