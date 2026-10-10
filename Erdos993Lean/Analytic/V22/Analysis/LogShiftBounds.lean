module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript: the logarithmic amplitude constants

Source: note Lemma 3.9(b,c). The four expressions below are exactly the four
parity formulas displayed in its proof. Consumer: the central-binomial
amplitudes `a_U` and `a_L`, followed by the activity-one log-ratio shift.
These estimates retain their indexed binomial atom; no forest process record
is reconstructed or promoted from a scalar estimate.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

/-- Note Lemma 3.9(b), the elementary upper bound for `log(1+x)`. -/
theorem logShift_log_one_add_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have h := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
  linarith

/-- Note Lemma 3.9(b,c), the elementary degree-two lower bound. -/
theorem logShift_log_one_add_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 2 / 2 ≤ Real.log (1 + x) := by
  apply le_trans ?_ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0 < x + 2)).2
  nlinarith [mul_nonneg hx (sq_nonneg x)]

/-- Note Lemma 3.9(c), the exact degree-three upper bound. -/
theorem logShift_log_one_add_upper {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let f : ℝ → ℝ := fun y => y - y ^ 2 / 2 + y ^ 3 / 3 - Real.log (1 + y)
  have hd : ∀ y ∈ Ici (0 : ℝ), HasDerivAt f (y ^ 3 / (1 + y)) y := by
    intro y hy
    have hy0 : 0 ≤ y := hy
    have hne : 1 + y ≠ 0 := ne_of_gt (by linarith)
    convert (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
      ((hasDerivAt_pow 3 y).div_const 3)).sub
      (((hasDerivAt_id y).const_add 1).log hne) using 1
    · funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq]
      dsimp [f]
    · dsimp [f]
      norm_num
      field_simp [hne]
      ring
  have hc : ContinuousOn f (Ici (0 : ℝ)) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Ici (0 : ℝ)) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hc
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy0 : 0 ≤ y := interior_subset hy
        positivity)
  have h := hm (by simp : (0 : ℝ) ∈ Ici 0) hx hx
  dsimp [f] at h
  norm_num at h
  linarith

/-- Note Lemma 3.9(b), the elementary lower bound for `-log(1-x)`. -/
theorem logShift_neg_log_one_sub_lower {x : ℝ} (hx : x < 1) :
    x ≤ -Real.log (1 - x) := by
  have h := Real.log_le_sub_one_of_pos (sub_pos.mpr hx)
  linarith

/-- Note Lemma 3.9(b), the exact cubic remainder bound for `-log(1-x)`. -/
theorem logShift_neg_log_one_sub_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -Real.log (1 - x) ≤ x + x ^ 2 / 2 + x ^ 3 / (3 * (1 - x)) := by
  let f : ℝ → ℝ := fun y => y + y ^ 2 / 2 + (y ^ 3 / 3) / (1 - y) +
    Real.log (1 - y)
  have hd : ∀ y ∈ Icc (0 : ℝ) x,
      HasDerivAt f (y ^ 3 / (3 * (1 - y) ^ 2)) y := by
    intro y hy
    have hne : 1 - y ≠ 0 := ne_of_gt (by linarith [hy.2])
    convert (((hasDerivAt_id y).add ((hasDerivAt_pow 2 y).div_const 2)).add
      (((hasDerivAt_pow 3 y).div_const 3).div ((hasDerivAt_id y).const_sub 1) hne)).add
      (((hasDerivAt_id y).const_sub 1).log hne) using 1
    · funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, id_eq]
      dsimp [f]
    · dsimp [f]
      norm_num
      field_simp [hne]
      ring
  have hc : ContinuousOn f (Icc (0 : ℝ) x) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) x) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) hc
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy0 : 0 ≤ y := (interior_subset hy : y ∈ Icc 0 x).1
        positivity)
  have h := hm ⟨le_rfl, hx0⟩ ⟨hx0, le_rfl⟩ hx0
  have heq : (x ^ 3 / 3) / (1 - x) = x ^ 3 / (3 * (1 - x)) := by
    field_simp
  dsimp [f] at h
  norm_num at h
  rw [heq] at h
  linarith

/-- The exact rational remainder estimate used at `x=1/N`, `N≥10`. -/
theorem logShift_neg_log_one_sub_small_upper {x : ℝ} (hx0 : 0 ≤ x)
    (hx1 : x ≤ 1 / 10) : -Real.log (1 - x) ≤ x + (43 / 80 : ℝ) * x ^ 2 := by
  have hxlt : x < 1 := by linarith
  have h := logShift_neg_log_one_sub_upper hx0 hxlt
  have hr : x ^ 3 / (3 * (1 - x)) ≤ (3 / 80 : ℝ) * x ^ 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 3 * (1 - x))).2
    have hcoef : 80 * x ≤ 9 * (1 - x) := by linarith
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr hcoef)]
  linarith

/-- Note Lemma 3.9(b), even upper amplitude. -/
noncomputable def logShiftUpperEven (N : ℝ) : ℝ :=
  -Real.log (1 - 1 / N) - (1 / 2) * Real.log (1 + 1 / (2 * N))

/-- Note Lemma 3.9(b), odd upper amplitude. -/
noncomputable def logShiftUpperOdd (N : ℝ) : ℝ :=
  -Real.log (1 - 1 / N) + 1 / (2 * (N + 1)) -
    (1 / 2) * Real.log (1 + 3 / (2 * N))

/-- Note Lemma 3.9(b), even lower amplitude. -/
noncomputable def logShiftLowerEven (N : ℝ) : ℝ :=
  -Real.log (1 - 1 / N) + 1 / (12 * N + 1) - 1 / (3 * N) -
    1 / (12 * (N - 1))

/-- Note Lemma 3.9(b), odd lower amplitude. -/
noncomputable def logShiftLowerOdd (N : ℝ) : ℝ :=
  -Real.log (1 - 1 / N) - (1 / 2) * Real.log (1 + 1 / N) +
    1 / (12 * N + 13) + 1 / (12 * (N + 1))

theorem logShift_inv_small {N : ℝ} (hN : 10 ≤ N) :
    0 < 1 / N ∧ 1 / N ≤ 1 / 10 := by
  constructor
  · positivity
  · apply (div_le_div_iff₀ (by linarith : 0 < N) (by norm_num : (0 : ℝ) < 10)).2
    linarith

/-- Note Lemma 3.9(b), the even upper expression has the stated upper bound. -/
theorem logShift_upper_even_le {N : ℝ} (hN : 10 ≤ N) :
    logShiftUpperEven N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2 := by
  have hx := logShift_inv_small hN
  have hl := logShift_neg_log_one_sub_small_upper hx.1.le hx.2
  have hp := logShift_log_one_add_lower (by positivity : 0 ≤ 1 / (2 * N))
  have heq : 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2 =
      (3 / 4 : ℝ) * (1 / N) + (11 / 10 : ℝ) * (1 / N) ^ 2 := by
    field_simp
  have heq2 : (1 : ℝ) / (2 * N) = (1 / N) / 2 := by ring
  rw [heq2] at hp
  rw [heq]
  unfold logShiftUpperEven
  rw [heq2]
  nlinarith [sq_nonneg (1 / N)]

/-- Note Lemma 3.9(b), the odd upper expression has the stated upper bound. -/
theorem logShift_upper_odd_le {N : ℝ} (hN : 10 ≤ N) :
    logShiftUpperOdd N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2 := by
  have hx := logShift_inv_small hN
  have hl := logShift_neg_log_one_sub_small_upper hx.1.le hx.2
  have hp := logShift_log_one_add_lower (by positivity : 0 ≤ 3 / (2 * N))
  have hf : 1 / (2 * (N + 1)) ≤ (1 / N) / 2 := by
    have h := (one_div_le_one_div_of_le (by linarith : 0 < N) (by linarith : N ≤ N + 1))
    have heq : (1 : ℝ) / (2 * (N + 1)) = (1 / (N + 1)) / 2 := by
      field_simp
    rw [heq]
    linarith
  have heq : 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2 =
      (3 / 4 : ℝ) * (1 / N) + (11 / 10 : ℝ) * (1 / N) ^ 2 := by
    field_simp
  have heq2 : (3 : ℝ) / (2 * N) = 3 * (1 / N) / 2 := by ring
  rw [heq2] at hp
  rw [heq]
  unfold logShiftUpperOdd
  rw [heq2]
  nlinarith

/-- Note Lemma 3.9(b), its even lower-amplitude rational comparison. -/
theorem logShift_even_correction_ge {N : ℝ} (hN : 10 ≤ N) :
    -(1 / 10 : ℝ) / N ^ 2 ≤ 1 / (12 * N + 1) - 1 / (12 * (N - 1)) := by
  have hn : 0 < N := by linarith
  have ha : 0 < 12 * N + 1 := by linarith
  have hb : 0 < 12 * (N - 1) := by linarith
  have hNm1 : N - 1 ≠ 0 := ne_of_gt (by linarith : 0 < N - 1)
  have heq : 1 / (12 * N + 1) - 1 / (12 * (N - 1)) =
      -(13 / ((12 * N + 1) * (12 * (N - 1)))) := by
    field_simp [ha.ne', hb.ne', hNm1]
    ring
  rw [heq, neg_div]
  apply neg_le_neg
  apply (div_le_div_iff₀ (mul_pos ha hb) (by positivity : 0 < N ^ 2)).2
  nlinarith [mul_nonneg (sub_nonneg.mpr hN) hn.le]

/-- Note Lemma 3.9(b), the even lower expression has the stated lower bound. -/
theorem logShift_lower_even_ge {N : ℝ} (hN : 10 ≤ N) :
    (13 / 20 : ℝ) / N ≤ logShiftLowerEven N := by
  have hx := logShift_inv_small hN
  have hl := logShift_neg_log_one_sub_lower (by linarith : 1 / N < 1)
  have hr := logShift_even_correction_ge hN
  have heqneg : -(1 / 10 : ℝ) / N ^ 2 = -(1 / 10 : ℝ) * (1 / N) ^ 2 := by
    field_simp
  have heq2 : (13 / 20 : ℝ) / N = (13 / 20 : ℝ) * (1 / N) := by ring
  have heq3 : (1 : ℝ) / (3 * N) = (1 / N) / 3 := by ring
  rw [heqneg] at hr
  rw [heq2]
  unfold logShiftLowerEven
  rw [heq3]
  nlinarith [mul_nonneg hx.1.le (sub_nonneg.mpr hx.2)]

/-- Note Lemma 3.9(b), the odd lower expression has the stated lower bound. -/
theorem logShift_lower_odd_ge {N : ℝ} (hN : 10 ≤ N) :
    (13 / 20 : ℝ) / N ≤ logShiftLowerOdd N := by
  have hn : 0 < N := by linarith
  have hl := logShift_neg_log_one_sub_lower
    (by linarith [(logShift_inv_small hN).2] : 1 / N < 1)
  have hp := logShift_log_one_add_le (by positivity : 0 ≤ 1 / N)
  have hr : 3 / (20 * N) ≤ 2 / (12 * N + 13) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    linarith
  rw [show (2 : ℝ) / (12 * N + 13) = 2 * (1 / (12 * N + 13)) by ring] at hr
  have hr2 : (1 : ℝ) / (12 * N + 13) ≤ 1 / (12 * (N + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have heq : (13 / 20 : ℝ) / N = (1 / 2) * (1 / N) + 3 / (20 * N) := by
    field_simp
    norm_num
  rw [heq]
  unfold logShiftLowerOdd
  nlinarith

/-- Note Lemma 3.9(b), fact-check's corrected even `L_N≤U_N` proof. -/
theorem logShift_lower_even_le_upper {N : ℝ} (hN : 10 ≤ N) :
    logShiftLowerEven N ≤ logShiftUpperEven N := by
  have hn : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hp := logShift_log_one_add_le (by positivity : 0 ≤ 1 / (2 * N))
  have hr : (1 : ℝ) / (12 * N + 1) ≤ 1 / (12 * N) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have ht : (0 : ℝ) ≤ 1 / (12 * (N - 1)) := by positivity
  have heq : (1 : ℝ) / (3 * N) = 1 / (12 * N) + (1 / 2) * (1 / (2 * N)) := by
    field_simp
    ring
  unfold logShiftLowerEven logShiftUpperEven
  rw [heq]
  linarith

/-- Note Lemma 3.9(b), fact-check's corrected odd `L_N≤U_N` proof. -/
theorem logShift_lower_odd_le_upper {N : ℝ} (hN : 10 ≤ N) :
    logShiftLowerOdd N ≤ logShiftUpperOdd N := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hlog : Real.log (1 + 3 / (2 * N)) - Real.log (1 + 1 / N) =
      Real.log (1 + 1 / (2 * (N + 1))) := by
    rw [← Real.log_div (by positivity : (1 + 3 / (2 * N) : ℝ) ≠ 0)
      (by positivity : (1 + 1 / N : ℝ) ≠ 0)]
    congr 1
    field_simp [hn.ne', hn1.ne']
    ring
  have hp := logShift_log_one_add_le (by positivity : 0 ≤ 1 / (2 * (N + 1)))
  have hr : (1 : ℝ) / (12 * N + 13) ≤ 1 / (12 * (N + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have heq : (1 : ℝ) / (2 * (N + 1)) = 6 * (1 / (12 * (N + 1))) := by
    field_simp
    norm_num
  have hdiff : Real.log (1 + 3 / (2 * N)) - Real.log (1 + 1 / N) ≤
      6 * (1 / (12 * (N + 1))) := by
    rw [hlog]
    exact hp.trans_eq heq
  have ht : (0 : ℝ) ≤ 1 / (12 * (N + 1)) := by positivity
  unfold logShiftLowerOdd logShiftUpperOdd
  rw [heq]
  nlinarith

/-- Note Lemma 3.9(b), all four exact parity formulas with its exact constants. -/
theorem logShift_four_formula_bounds {N : ℝ} (hN : 10 ≤ N) :
    ((13 / 20 : ℝ) / N ≤ logShiftUpperEven N ∧
      logShiftUpperEven N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2) ∧
    ((13 / 20 : ℝ) / N ≤ logShiftUpperOdd N ∧
      logShiftUpperOdd N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2) ∧
    ((13 / 20 : ℝ) / N ≤ logShiftLowerEven N ∧
      logShiftLowerEven N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2) ∧
    ((13 / 20 : ℝ) / N ≤ logShiftLowerOdd N ∧
      logShiftLowerOdd N ≤ 3 / (4 * N) + (11 / 10 : ℝ) / N ^ 2) := by
  have hle := logShift_lower_even_le_upper hN
  have hlo := logShift_lower_odd_le_upper hN
  have hge := logShift_lower_even_ge hN
  have hgo := logShift_lower_odd_ge hN
  have hue := logShift_upper_even_le hN
  have huo := logShift_upper_odd_le hN
  exact ⟨⟨hge.trans hle, hue⟩, ⟨hgo.trans hlo, huo⟩, ⟨hge, hle.trans hue⟩,
    ⟨hgo, hlo.trans huo⟩⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_le
#check Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_lower
#check Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_log_one_add_upper
#check Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_lower
#check Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_upper
#check Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_small_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_neg_log_one_sub_small_upper
#check Erdos993Lean.Analytic.V22.Analysis.logShiftUpperEven
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftUpperEven
#check Erdos993Lean.Analytic.V22.Analysis.logShiftUpperOdd
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftUpperOdd
#check Erdos993Lean.Analytic.V22.Analysis.logShiftLowerEven
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftLowerEven
#check Erdos993Lean.Analytic.V22.Analysis.logShiftLowerOdd
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftLowerOdd
#check Erdos993Lean.Analytic.V22.Analysis.logShift_inv_small
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_inv_small
#check Erdos993Lean.Analytic.V22.Analysis.logShift_upper_even_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_upper_even_le
#check Erdos993Lean.Analytic.V22.Analysis.logShift_upper_odd_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_upper_odd_le
#check Erdos993Lean.Analytic.V22.Analysis.logShift_even_correction_ge
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_even_correction_ge
#check Erdos993Lean.Analytic.V22.Analysis.logShift_lower_even_ge
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_lower_even_ge
#check Erdos993Lean.Analytic.V22.Analysis.logShift_lower_odd_ge
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_lower_odd_ge
#check Erdos993Lean.Analytic.V22.Analysis.logShift_lower_even_le_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_lower_even_le_upper
#check Erdos993Lean.Analytic.V22.Analysis.logShift_lower_odd_le_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_lower_odd_le_upper
#check Erdos993Lean.Analytic.V22.Analysis.logShift_four_formula_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_four_formula_bounds
