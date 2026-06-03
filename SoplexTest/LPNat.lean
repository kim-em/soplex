import Soplex

/-!
`by lp` / `maximize` over `Nat` (ordered commutative semiring, no negation).
With no subtraction the certificate is a two-sided weighted sum `Wl ≤ Wr` plus
the semiring identity `L·rhs + Wl = L·lhs + Wr + C`. Goals must be `Nat.sub`-free.
-/

-- Atomic weighted combination (`2a + b ≤ 5`, `a + b ≤ 3` ⊢ `3a + 2b ≤ 8`).
example (a b : Nat) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a + b ≤ 3) : 3 * a + 2 * b ≤ 8 := by lp

-- Box-LP shape.
example (x y : Nat) (_h₁ : x ≤ 1) (_h₂ : y ≤ 1) : x + y ≤ 2 := by lp

-- Strict goal.
example (a b : Nat) (_h₁ : 2 * a + b ≤ 4) (_h₂ : a + b ≤ 1) : 3 * a + 2 * b < 8 := by lp

-- Equality goal.
example (a b : Nat) (_h₁ : a + b ≤ 3) (_h₂ : 3 ≤ a + b) : a + b = 3 := by lp

-- Equality HYPOTHESIS used with a nonzero multiplier (the no-subtraction
-- assembly must expose both ≤-directions of `=` as weighted-sum rows).
example (a b : Nat) (_h : a + b = 3) : 2 * a + 2 * b ≤ 6 := by lp
example (a b c : Nat) (_h₁ : a + b = 3) (_h₂ : c ≤ 1) : a + b + c ≤ 4 := by lp

-- Cleared multiplier (L = 2).
example (x : Nat) (_h : 2 * x ≤ 6) : x ≤ 3 := by lp

-- Infeasible hypotheses: any (comparison) goal follows by Farkas.
example (a : Nat) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : a ≤ 0 := by lp

-- Existential (nonneg-integer witnesses).
example : ∃ x : Nat, 2 ≤ x ∧ x ≤ 4 := by lp
example : ∃ x y : Nat, x ≤ 3 ∧ y ≤ 2 ∧ 1 ≤ x := by lp

-- maximize.
example (x : Nat) (_h : 2 * x ≤ 6) : True := by
  maximize (x : Nat)
  trivial

-- Inconsistent hypotheses also close a bare `False` goal (carrier from hyps),
-- including when the inconsistency is inside an `∧` hypothesis.
example (a : Nat) (_h₁ : a ≤ 1) (_h₂ : 3 ≤ a) : False := by lp
example (a : Nat) (_h : a ≤ 1 ∧ 3 ≤ a) : False := by lp
