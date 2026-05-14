import Soplex

/-!
These probes intentionally assert failure for now. The parser/solver gate
can recognise these examples, but `lp` must not close them by delegating to
`grind`; certificate proof reconstruction is still required.
-/

example (a b : Rat) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : True := by
  fail_if_success (have : 3 * a ≤ 6 := by lp)
  trivial

example (a b : Rat) (_h₁ : 5 ≥ 2 * a + b) (_h₂ : 1 ≥ a - b) : True := by
  fail_if_success (have : 6 ≥ 3 * a := by lp)
  trivial

example (n : Nat) (x : Rat) (_hn : 0 ≤ n) (_h : x ≤ 0) : True := by
  fail_if_success (have : x ≤ 0 := by lp)
  trivial

example (x : Rat) (_h : x ≤ 0) : True := by
  fail_if_success (have : x < 1 := by lp)
  trivial

example (x y : Rat) (_h : (1 / 2 : Rat) * x + y ≤ 1) : True := by
  fail_if_success (have : x + 2 * y ≤ 2 := by lp)
  trivial

example (a : Rat) (_h : a ≤ 0 ∧ 0 ≤ a) : True := by
  fail_if_success (have : a = 0 := by lp)
  trivial

example (x : Rat) (h : x ≤ 1) : True := by
  fail_if_success (have : x < 1 := by lp)
  fail_if_success (have : 1 > x := by lp)
  have _ := h
  trivial

example (x y : Rat) (_h : x ≤ 1) : True := by
  fail_if_success (have : y ≤ 0 := by lp)
  have _ := y
  trivial

example (x y : Rat) (_h : x * y ≤ 1) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (x : Rat) (_h : x < 1) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (x : Rat) (_h : 1 > x) : True := by
  fail_if_success (have : x ≤ 1 := by lp)
  trivial

example (x : Rat) : True := by
  fail_if_success (have : (let c : Rat := 3; c * x ≤ 3 * x) := by lp)
  have _ := x
  trivial

example (x : Rat) : True := by
  let c : Rat := 3
  fail_if_success (have : c * x ≤ 3 * x := by lp)
  have _ := x
  trivial

example (_c _x : Rat) : True := by
  fail_if_success (have : _c * _x ≤ _c * _x := by lp)
  trivial
