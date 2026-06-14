import LP

/-!
`by lp` never silently mis-models an operation whose carrier semantics are not the
exact rational arithmetic the parser assumes: `Nat` subtraction is truncating
(`Nat.sub`) and `Int`/`Nat` division is integer/floor division. `lp` atomizes such a
subterm as an opaque atom (it carries no truncation arithmetic), so the residual
linear problem cannot close, and `lp` then fails with a clear diagnostic pointing at
`cutsat`/`omega` rather than returning a wrong answer. (`Nat` has no `Neg` and
`Dyadic` no `Div`, so those never form.) `#guard_msgs` pins the exact message.
-/

/-- error: lp: this goal involves a truncating `Nat`-subtraction or `Int`/`Nat` floor-division/`%`, which `lp` atomized as an opaque term (it carries no truncation arithmetic) and could not close. Use `cutsat` (or `omega`) for goals that genuinely need truncation semantics. -/
#guard_msgs in
example (a b : Nat) (_h : a ≤ b) : a - b ≤ 0 := by lp

/-- error: lp: this goal involves a truncating `Nat`-subtraction or `Int`/`Nat` floor-division/`%`, which `lp` atomized as an opaque term (it carries no truncation arithmetic) and could not close. Use `cutsat` (or `omega`) for goals that genuinely need truncation semantics. -/
#guard_msgs in
example (a b : Nat) (_h : a - b ≤ 0) : a ≤ b := by lp

/-- error: lp: this goal involves a truncating `Nat`-subtraction or `Int`/`Nat` floor-division/`%`, which `lp` atomized as an opaque term (it carries no truncation arithmetic) and could not close. Use `cutsat` (or `omega`) for goals that genuinely need truncation semantics. -/
#guard_msgs in
example (a : Int) (_h : a ≤ 6) : a ≤ 12 / 2 := by lp

/-- error: lp: this goal involves a truncating `Nat`-subtraction or `Int`/`Nat` floor-division/`%`, which `lp` atomized as an opaque term (it carries no truncation arithmetic) and could not close. Use `cutsat` (or `omega`) for goals that genuinely need truncation semantics. -/
#guard_msgs in
example (a : Nat) (_h : a ≤ 3) : a ≤ 7 / 2 := by lp

-- Exact ring subtraction (`Int`/`Dyadic`) and field division (`Rat`) remain supported.
example (a b : Int) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a b : Dyadic) (_h₁ : 2 * a + b ≤ 5) (_h₂ : a - b ≤ 1) : 3 * a ≤ 6 := by lp
example (a : Rat) (_h : 3 * a ≤ 1) : a ≤ 1 / 3 := by lp
