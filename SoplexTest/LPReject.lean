import Soplex

/-!
`by lp` rejects operations whose carrier semantics are not the exact rational
arithmetic the parser assumes, instead of silently mis-modelling them into a wrong
LP: `Nat` subtraction is truncating (`Nat.sub`) and `Int`/`Nat` division is
integer/floor division. Each is refused at parse time with a clear error pointing
at `cutsat`/`omega`. (`Nat` has no `Neg` and `Dyadic` no `Div`, so those never
form.) `#guard_msgs` pins the exact messages.
-/

/-- error: lp: subtraction over `Nat` is truncating (`Nat.sub`) and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Nat` subtraction -/
#guard_msgs in
example (a b : Nat) (_h : a ≤ b) : a - b ≤ 0 := by lp

/-- error: lp: subtraction over `Nat` is truncating (`Nat.sub`) and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Nat` subtraction -/
#guard_msgs in
example (a b : Nat) (_h : a - b ≤ 0) : True := by lp

/-- error: lp: division over `Int` is integer/truncating division and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Int`/`Nat` division -/
#guard_msgs in
example (a : Int) (_h : a ≤ 6) : a ≤ 12 / 2 := by lp

/-- error: lp: division over `Nat` is integer/truncating division and is not supported by `lp`; use `cutsat` (or `omega`) for goals involving `Int`/`Nat` division -/
#guard_msgs in
example (a : Nat) (_h : a ≤ 3) : a ≤ 7 / 2 := by lp

-- Exact ring subtraction (`Int`/`Dyadic`) and field division (`Rat`) remain supported.
example (a b : Int) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Dyadic) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a : Rat) (_h : 3 * a ≤ 1) : a ≤ 1 / 3 := by lp
