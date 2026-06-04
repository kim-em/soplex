/-
Exp 2 — normalizer strategy: bespoke `IntModule` algebra vs reflective `Poly`.

lp's current normalizer (`normalizeR`/`proveMerge`/`proveSmul`/`proveNeg` in
`Certificate.lean`) proves the closed certificate identity by a hand-rolled,
`Rat`/`Q`-specific merge with `take_left`/`take_right`/`combine` lemmas. This
experiment asks: once coefficients are integers (after Exp 1 clearing), can the
identity instead be discharged by Lean core's reflective `Lean.Grind.Linarith`
engine, generically over any `IntModule`?

Finding (see bottom): the reflective route discharges an arbitrary linear
cancellation identity with a single `rfl` on the normal-form `Poly`, regardless
of size, with zero bespoke lemmas — whereas core has no `abel`/`ring`, so the
bespoke route must drive abelian-group rewrites by hand.

No soplex, no Mathlib — only Lean core `Grind`.
-/
import Init.Grind.Ordered.Linarith

namespace Exp2

open Std
open Lean.Grind
open Lean.Grind.Linarith

/-! ## Reflective route -/

/-- The one reusable bridge: equal normal forms ⇒ equal denotations, for any
`IntModule`. Everything else is `rfl` on `Poly`. -/
theorem of_norm_eq {α} [IntModule α] (ctx : Context α) (e₁ e₂ : Expr)
    (h : e₁.norm = e₂.norm) : e₁.denote ctx = e₂.denote ctx := by
  rw [← Expr.denote_norm ctx e₁, ← Expr.denote_norm ctx e₂, h]

section
variable {M : Type u} [IntModule M]

-- A genuine cancellation: `3•x + 2•y + (-3)•x + (-2)•y = 0`.
-- Reified as a `Linarith.Expr` over the context `[x ↦ var 0, y ↦ var 1]`.
private def cancelE : Expr :=
  .add (.add (.intMul 3 (.var 0)) (.intMul 2 (.var 1)))
       (.add (.intMul (-3) (.var 0)) (.intMul (-2) (.var 1)))

-- Reflective proof: the normal form is `.nil` (== `Expr.zero.norm`), checked by
-- `rfl`; `of_norm_eq` then transports to the denotation. This same two-liner
-- works for ANY linear identity, of any size, over any `IntModule`.
example (x y : M) :
    cancelE.denote (.branch 1 (.leaf x) (.leaf y)) = (0 : M) := by
  have h := of_norm_eq (.branch 1 (.leaf x) (.leaf y)) cancelE .zero (by rfl)
  simpa [Expr.denote] using h

end

/-! ## Bespoke route (same identity, hand-driven abelian-group algebra) -/

section
open Lean.Grind.IntModule Lean.Grind.AddCommGroup
variable {M : Type u} [IntModule M]

-- The same cancellation, proved directly. Core has no `abel`/`ring`, so every
-- regrouping/cancellation step is explicit. This is what a generic bespoke
-- normalizer would have to automate per certificate.
example (x y : M) :
    (3 : Int) • x + (2 : Int) • y + ((-3 : Int) • x + (-2 : Int) • y) = (0 : M) := by
  rw [show ((-3 : Int)) • x = -((3 : Int) • x) by rw [← neg_zsmul]]
  rw [show ((-2 : Int)) • y = -((2 : Int) • y) by rw [← neg_zsmul]]
  rw [← neg_add, add_neg_cancel]

end

/-
Head-to-head verdict (recorded for decision 4):

* Reflective: `of_norm_eq` (one 3-line bridge, written once) + a `(by rfl)` on the
  `Poly` normal form. The proof term is independent of the number of monomials;
  the kernel computes `Expr.norm` (sorted-insert fusion) and checks structural
  equality. No per-shape lemmas. Generic over every `IntModule`. The cost is
  building the `Linarith.Expr` + `RArray` context at tactic time (Exp 5).
  LIMITATION: `Linarith.Expr` has no constant constructor — numeric constants
  must be modeled as a pinned `1`-variable (as grind itself does), and the
  residual-positivity step still needs the Exp 0 closer (+ `OrderedRing`).

* Bespoke: no reflection plumbing, but every identity is hand-driven abelian
  algebra (above), because core ships no `abel`/`ring`. Porting lp's existing
  `proveMerge`/`take_left`/`take_right`/`combine` from `Rat`/`Q` to integer
  coefficients over `IntModule` reproduces a verified linear-merge engine — i.e.
  re-deriving exactly what `Linarith.Poly.combine`/`denote_combine` already give.

Recommendation: prefer the REFLECTIVE `Poly` for the normalizer — it deletes the
hand-rolled merge entirely and is already verified. Keep the bespoke closer
(Exp 0) for the final inequality/positivity step, which `Poly` does not cover.
-/

end Exp2
