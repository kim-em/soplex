/-
  Soundness theorems bridging the `Bool` checkers in
  `LeanSoplex.Verify.Bool` to the `Prop` predicates in
  `LeanSoplex.Verify.Prop`.

  The central proof obligation is `weak_duality` on `Rat`. The three
  certificate-soundness lemmas (`checkOptimal_sound`,
  `checkInfeasible_sound`, `checkUnbounded_sound`) follow from
  `weak_duality` plus the certificate-specific equalities / strict
  inequalities.

  All theorems are currently stated with their proofs deferred via
  `sorry`. They are the main pure-Lean work item that remains
  outstanding from `PLAN.md`; see issue tracker.
-/

import LeanSoplex.Verify.Arith

namespace LeanSoplex.Verify

open LeanSoplex

private theorem problemShapeOk_of_prop {p : Problem}
    (h : ProblemShapeOk p) : problemShapeOk p = true := by
  unfold problemShapeOk
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact decide_eq_true h.c_size
  · exact decide_eq_true h.colBounds_size
  · exact decide_eq_true h.rowBounds_size
  · rw [Array.all_eq_true]
    intro k hk
    have hrange := h.sparse_in_range k hk
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true hrange.1, decide_eq_true hrange.2⟩

private theorem dualShapeOk
    {p : Problem} {d : DualBundle}
    (hShape : ProblemShapeOk p)
    (hDual : DualNonnegZeroWhereAbsent p d) :
    problemShapeOk p
     && decide (d.rowLower.size = p.numConstraints)
     && decide (d.rowUpper.size = p.numConstraints)
     && decide (d.colLower.size = p.numVars)
     && decide (d.colUpper.size = p.numVars) = true := by
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨⟨⟨problemShapeOk_of_prop hShape,
    by simp [hDual.rowLower_size]⟩,
    by simp [hDual.rowUpper_size]⟩,
    by simp [hDual.colLower_size]⟩,
    by simp [hDual.colUpper_size]⟩

private theorem dualNonnegAndZeroWhereAbsent_imp_shape
    {p : Problem} {d : DualBundle}
    (h : dualNonnegAndZeroWhereAbsent p d = true) :
    ProblemShapeOk p := by
  unfold dualNonnegAndZeroWhereAbsent at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true] at h
  exact problemShapeOk_imp h.1.1.1.1.1.1

private theorem isDualFeasible_imp
    {p : Problem} {d : DualBundle}
    (h : isDualFeasible p d = true) :
    ProblemShapeOk p ∧ IsDualFeasible p d := by
  unfold isDualFeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hNonneg, hStatBool⟩ := h
  have hShape := dualNonnegAndZeroWhereAbsent_imp_shape hNonneg
  have hDual := dualNonnegAndZeroWhereAbsent_imp hNonneg
  refine ⟨hShape, ?_⟩
  exact { nonneg_zero_absent := hDual
          stationarity := isStationary_imp hShape hDual hStatBool }

private theorem range_fold_mono
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i ≤ g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 ≤
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      exact RatAux.add_le_add
        (by simpa using ih (by intro i hi; exact h i (by omega)))
        (h n (by omega))

private theorem range_fold_congr
    (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i < n → f i = g i) :
    (Array.range n).foldl (fun acc i => acc + f i) 0 =
      (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  apply Rat.le_antisymm
  · exact range_fold_mono n f g (by
      intro i hi
      rw [h i hi]
      exact Rat.le_refl)
  · exact range_fold_mono n g f (by
      intro i hi
      rw [h i hi]
      exact Rat.le_refl)

private theorem range_fold_add
    (n : Nat) (f g : Nat → Rat) :
    (Array.range n).foldl (fun acc i => acc + (f i + g i)) 0 =
      (Array.range n).foldl (fun acc i => acc + f i) 0 +
        (Array.range n).foldl (fun acc i => acc + g i) 0 := by
  induction n with
  | zero =>
      simp [Array.range, Rat.zero_add]
  | succ n ih =>
      simp [Array.range_succ]
      have ih' :
          Array.foldl (fun acc i => acc + (f i + g i)) 0 (Array.range n) 0 n =
            Array.foldl (fun acc i => acc + f i) 0 (Array.range n) 0 n +
              Array.foldl (fun acc i => acc + g i) 0 (Array.range n) 0 n := by
        simpa using ih
      rw [ih']
      grind [Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem range_fold_mono_sub
    (n : Nat) (f g h : Nat → Rat)
    (hle : ∀ i, i < n → f i - g i ≤ h i) :
    (Array.range n).foldl (fun acc i => acc + f i - g i) 0 ≤
      (Array.range n).foldl (fun acc i => acc + h i) 0 := by
  induction n with
  | zero =>
      simp [Array.range]
  | succ n ih =>
      simp [Array.range_succ]
      have hprev :
          Array.foldl (fun acc i => acc + f i - g i) 0 (Array.range n) 0 n ≤
            Array.foldl (fun acc i => acc + h i) 0 (Array.range n) 0 n := by
        simpa using ih (by intro i hi; exact hle i (by omega))
      have hadd := RatAux.add_le_add hprev (hle n (by omega))
      grind [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_comm, Rat.add_left_comm]

private theorem lower_contrib_le {lo : Option Rat} {mult value : Rat}
    (hNonneg : 0 ≤ mult)
    (hBound : ∀ l, lo = some l → l ≤ value)
    (hZero : lo = none → mult = 0) :
    (lo.elim 0 (mult * ·)) ≤ mult * value := by
  cases lo with
  | none =>
      simp [hZero rfl]
  | some l =>
      exact Rat.mul_le_mul_of_nonneg_left (hBound l rfl) hNonneg

private theorem neg_upper_contrib_le {hi : Option Rat} {mult value : Rat}
    (hNonneg : 0 ≤ mult)
    (hBound : ∀ u, hi = some u → value ≤ u)
    (hZero : hi = none → mult = 0) :
    -(hi.elim 0 (mult * ·)) ≤ -(mult * value) := by
  cases hi with
  | none =>
      simp [hZero rfl]
  | some u =>
      exact Rat.neg_le_neg (Rat.mul_le_mul_of_nonneg_left (hBound u rfl) hNonneg)

private theorem bound_term_le
    {lo hi : Option Rat} {loMult hiMult value : Rat}
    (hLoNonneg : 0 ≤ loMult) (hHiNonneg : 0 ≤ hiMult)
    (hLoBound : ∀ l, lo = some l → l ≤ value)
    (hHiBound : ∀ u, hi = some u → value ≤ u)
    (hLoZero : lo = none → loMult = 0)
    (hHiZero : hi = none → hiMult = 0) :
    lo.elim 0 (loMult * ·) - hi.elim 0 (hiMult * ·) ≤
      (loMult - hiMult) * value := by
  have hLo := lower_contrib_le (lo := lo) hLoNonneg hLoBound hLoZero
  have hHi := neg_upper_contrib_le (hi := hi) hHiNonneg hHiBound hHiZero
  have h := RatAux.add_le_add hLo hHi
  grind [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]

private theorem dot_of_stationarity
    {p : Problem} {d : DualBundle} {x q : Array Rat}
    (hShape : ProblemShapeOk p)
    (hXSize : x.size = p.numVars)
    (hDual : DualNonnegZeroWhereAbsent p d)
    (hStat : StationarityAgainst p d q)
    (hQ : q.size = p.numVars) :
    dot q x =
      dot (evalATy p (arraySub d.rowLower d.rowUpper)) x +
        dot (arraySub d.colLower d.colUpper) x := by
  have hColEq : d.colLower.size = d.colUpper.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hAty : (evalATy p (arraySub d.rowLower d.rowUpper)).size = p.numVars :=
    evalATy_size ..
  have hZdiff : (arraySub d.colLower d.colUpper).size = p.numVars := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  rw [dot_eq_range_fold q x (by rw [hQ, hXSize])]
  rw [dot_eq_range_fold (evalATy p (arraySub d.rowLower d.rowUpper)) x
    (by rw [hAty, hXSize])]
  rw [dot_eq_range_fold (arraySub d.colLower d.colUpper) x
    (by rw [hZdiff, hXSize])]
  rw [hQ, hAty, hZdiff]
  rw [← range_fold_add p.numVars
    (fun j => (evalATy p (arraySub d.rowLower d.rowUpper))[j]! * x[j]!)
    (fun j => (arraySub d.colLower d.colUpper)[j]! * x[j]!)]
  apply range_fold_congr
  intro j hj
  have hjQ : j < q.size := by rw [hQ]; exact hj
  have hjA : j < (evalATy p (arraySub d.rowLower d.rowUpper)).size := by
    rw [hAty]; exact hj
  have hjZ : j < (arraySub d.colLower d.colUpper).size := by
    rw [hZdiff]; exact hj
  have hStatj := hStat j hj
  have hSub := arraySub_get!_of_eq d.colLower d.colUpper hColEq j
    (by rw [hDual.colLower_size]; exact hj)
  rw [hSub]
  rw [← hStatj]
  grind [Rat.mul_add]

private theorem bound_combination_le_dot_q
    {p : Problem} {d : DualBundle} {x q : Array Rat}
    (hShape : ProblemShapeOk p)
    (hX : IsFeasible p x)
    (hDual : DualNonnegZeroWhereAbsent p d)
    (hStat : StationarityAgainst p d q)
    (hQ : q.size = p.numVars) :
    dualBoundCombination p d ≤ dot q x := by
  have hXSize : x.size = p.numVars := hX.1.1
  have hAxSize : (evalAx p x).size = p.numConstraints := evalAx_size ..
  have hRowEq : d.rowLower.size = d.rowUpper.size :=
    hDual.rowLower_size.trans hDual.rowUpper_size.symm
  have hColEq : d.colLower.size = d.colUpper.size :=
    hDual.colLower_size.trans hDual.colUpper_size.symm
  have hRowSub : (arraySub d.rowLower d.rowUpper).size = p.numConstraints := by
    rw [arraySub_size_of_eq _ _ hRowEq]; exact hDual.rowLower_size
  have hColSub : (arraySub d.colLower d.colUpper).size = p.numVars := by
    rw [arraySub_size_of_eq _ _ hColEq]; exact hDual.colLower_size
  have hRowLe :
      (Array.range p.numConstraints).foldl (fun (acc : Rat) i =>
        let (lo, hi) := p.rowBounds[i]!
        acc + lo.elim 0 (d.rowLower[i]! * ·) -
          hi.elim 0 (d.rowUpper[i]! * ·)) 0 ≤
        dot (arraySub d.rowLower d.rowUpper) (evalAx p x) := by
    rw [dot_eq_range_fold (arraySub d.rowLower d.rowUpper) (evalAx p x)
      (by rw [hRowSub, hAxSize])]
    rw [hRowSub]
    exact range_fold_mono_sub p.numConstraints
      (fun i => (p.rowBounds[i]!).1.elim 0 (d.rowLower[i]! * ·))
      (fun i => (p.rowBounds[i]!).2.elim 0 (d.rowUpper[i]! * ·))
      (fun i => (arraySub d.rowLower d.rowUpper)[i]! * (evalAx p x)[i]!)
      (by
        intro i hi
        have hNon := hDual.row_nonneg i hi
        have hZero := hDual.row_zero_absent i hi
        have hBounds := hX.2 ⟨i, hi⟩
        have hSub := arraySub_get!_of_eq d.rowLower d.rowUpper hRowEq i
          (by rw [hDual.rowLower_size]; exact hi)
        calc
          (match p.rowBounds[i]! with
            | (lo, hi) =>
              (lo.elim 0 fun x => d.rowLower[i]! * x) -
                hi.elim 0 fun x => d.rowUpper[i]! * x)
              ≤ (d.rowLower[i]! - d.rowUpper[i]!) * (evalAx p x)[i]! := by
                exact bound_term_le hNon.1 hNon.2 hBounds.1 hBounds.2 hZero.1 hZero.2
          _ = (arraySub d.rowLower d.rowUpper)[i]! * (evalAx p x)[i]! := by
                rw [hSub])
  have hColLe :
      (Array.range p.numVars).foldl (fun (acc : Rat) j =>
        let (lo, hi) := p.colBounds[j]!
        acc + lo.elim 0 (d.colLower[j]! * ·) -
          hi.elim 0 (d.colUpper[j]! * ·)) 0 ≤
        dot (arraySub d.colLower d.colUpper) x := by
    rw [dot_eq_range_fold (arraySub d.colLower d.colUpper) x
      (by rw [hColSub, hXSize])]
    rw [hColSub]
    exact range_fold_mono_sub p.numVars
      (fun j => (p.colBounds[j]!).1.elim 0 (d.colLower[j]! * ·))
      (fun j => (p.colBounds[j]!).2.elim 0 (d.colUpper[j]! * ·))
      (fun j => (arraySub d.colLower d.colUpper)[j]! * x[j]!)
      (by
        intro j hj
        have hNon := hDual.col_nonneg j hj
        have hZero := hDual.col_zero_absent j hj
        have hBounds := hX.1.2 ⟨j, hj⟩
        have hSub := arraySub_get!_of_eq d.colLower d.colUpper hColEq j
          (by rw [hDual.colLower_size]; exact hj)
        calc
          (match p.colBounds[j]! with
            | (lo, hi) =>
              (lo.elim 0 fun x => d.colLower[j]! * x) -
                hi.elim 0 fun x => d.colUpper[j]! * x)
              ≤ (d.colLower[j]! - d.colUpper[j]!) * x[j]! := by
                exact bound_term_le hNon.1 hNon.2 hBounds.1 hBounds.2 hZero.1 hZero.2
          _ = (arraySub d.colLower d.colUpper)[j]! * x[j]! := by
                rw [hSub])
  have hBoundLe :
      dualBoundCombination p d ≤
        dot (arraySub d.rowLower d.rowUpper) (evalAx p x) +
          dot (arraySub d.colLower d.colUpper) x := by
    unfold dualBoundCombination
    simp [problemShapeOk_of_prop hShape, hDual.rowLower_size, hDual.rowUpper_size,
      hDual.colLower_size, hDual.colUpper_size]
    have hAdd := RatAux.add_le_add hRowLe hColLe
    simpa [Rat.sub_eq_add_neg] using hAdd
  have hBilin :
      dot (arraySub d.rowLower d.rowUpper) (evalAx p x) =
        dot (evalATy p (arraySub d.rowLower d.rowUpper)) x :=
    dot_y_evalAx_eq_dot_evalATy_x p (arraySub d.rowLower d.rowUpper) x
      hShape hRowSub hXSize
  have hDot := dot_of_stationarity hShape hXSize hDual hStat hQ
  rw [hBilin] at hBoundLe
  rw [hDot]
  exact hBoundLe

/-- Weak duality on `Rat`: any primal-feasible `x` and any dual-feasible
    `d` satisfy `dualObj d ≤ primalObj x`.

    Proof shape (per `PLAN.md` §"Verification layer"):

    1. Stationarity `Aᵀ(yL − yU) + (zL − zU) = c` lets us rewrite
       `c·x` as `Σⱼ (Aᵀ(yL − yU) + (zL − zU))ⱼ · xⱼ`.
    2. Swap finite sums to get
       `Σᵢ (yLᵢ − yUᵢ) · (Ax)ᵢ + Σⱼ (zLⱼ − zUⱼ) · xⱼ`.
    3. Use componentwise bound inequalities
       (`yLᵢ ≥ 0 ∧ (Ax)ᵢ ≥ rₗᵢ ⇒ yLᵢ · (Ax)ᵢ ≥ yLᵢ · rₗᵢ`, three
       symmetric variants) to lower-bound each term by its dual-obj
       contribution.
    4. The remaining shifted sum is exactly `dualObj p d`. -/
theorem weak_duality {p : Problem} {x : Array Rat} {d : DualBundle}
    (hx : isPrimalFeasible p x = true)
    (hd : isDualFeasible    p d = true) :
    dualObj p d ≤ primalObj p x := by
  obtain ⟨hShape, hFeas⟩ := isPrimalFeasible_imp hx
  obtain ⟨_, hDualFeas⟩ := isDualFeasible_imp hd
  have hBound := bound_combination_le_dot_q hShape hFeas
    hDualFeas.nonneg_zero_absent hDualFeas.stationarity hShape.c_size
  unfold dualObj primalObj
  exact Rat.add_le_add_right.mpr hBound

/-- Optimality certificate is sound: a Boolean-accepted certificate
    really witnesses feasibility and min-optimality. -/
theorem checkOptimal_sound {p : Problem} {x : Array Rat} {d : DualBundle}
    (h : checkOptimal p x d = true) :
    IsFeasible p x ∧ IsOptimalMin p x := by
  unfold checkOptimal at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hPrimal, hDualBool⟩, hEqBool⟩ := h
  obtain ⟨hShape, hFeasX⟩ := isPrimalFeasible_imp hPrimal
  obtain ⟨_, hDual⟩ := isDualFeasible_imp hDualBool
  have hEq : primalObj p x = dualObj p d := by
    simpa [beq_iff_eq] using hEqBool
  refine ⟨hFeasX, hFeasX, ?_⟩
  intro y hFeasY
  have hBound := bound_combination_le_dot_q hShape hFeasY
    hDual.nonneg_zero_absent hDual.stationarity hShape.c_size
  have hWeakY : dualObj p d ≤ primalObj p y := by
    unfold dualObj primalObj
    exact Rat.add_le_add_right.mpr hBound
  rw [hEq]
  exact hWeakY

/-- Infeasibility (Farkas) certificate is sound. -/
theorem checkInfeasible_sound {p : Problem} {d : DualBundle}
    (h : checkInfeasible p d = true) :
    IsInfeasible p := by
  unfold checkInfeasible at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hFarkasBool, hPosBool⟩ := h
  unfold isFarkasFeasible at hFarkasBool
  rw [Bool.and_eq_true] at hFarkasBool
  obtain ⟨hNonnegBool, hZeroBool⟩ := hFarkasBool
  have hShape := dualNonnegAndZeroWhereAbsent_imp_shape hNonnegBool
  have hFarkas := isFarkasFeasible_imp (by
    unfold isFarkasFeasible
    rw [Bool.and_eq_true]
    exact ⟨hNonnegBool, hZeroBool⟩)
  have hPos := boundCombinationPos_imp hPosBool
  intro hExists
  obtain ⟨x, hFeasX⟩ := hExists
  have hStatZero : StationarityAgainst p d (Array.replicate p.numVars 0) := by
    intro j hj
    simpa [getElem!_pos (Array.replicate p.numVars (0 : Rat)) j (by simpa using hj),
      Array.getElem_replicate] using hFarkas.stationarity_zero j hj
  have hLe := bound_combination_le_dot_q hShape hFeasX
    hFarkas.nonneg_zero_absent hStatZero (by simp)
  have hXSize : x.size = p.numVars := hFeasX.1.1
  rw [dot_replicate_left_zero' x p.numVars hXSize] at hLe
  have : False := by grind
  exact this.elim

/-- Unbounded certificate is sound. -/
theorem checkUnbounded_sound {p : Problem} {x ray : Array Rat}
    (_h : checkUnbounded p x ray = true) :
    IsUnboundedMin p := by
  sorry

end LeanSoplex.Verify
