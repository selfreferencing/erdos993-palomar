module

public import Erdos993Lean.Analytic.V22.Analysis.LogShiftBounds

/-!
# Version 2.2 of the manuscript: exact `k_X` constants

Source: note Lemma 3.9(c), with the same formula as Lemma 3.9(a).
Consumer: the activity-one log-ratio shift. The final theorem applies to each
of the four exact parity expressions; its only hypothesis is `M≥8`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

/-- Note Lemma 3.9(a), `k_X` as a function of its logarithmic amplitude. -/
noncomputable def logShiftKValue (M A : ℝ) : ℝ :=
  (M + 3) * ((5 / 2) * Real.log (1 + 2 / M) - 1 / (2 * (M + 3)) - A)

/-- Note Lemma 3.9(c), the two weighted Taylor comparisons. -/
theorem logShift_weighted_log_bounds {M : ℝ} (hM : 8 ≤ M) :
    5 + 10 / M - 15 / M ^ 2 ≤ (5 / 2) * (M + 3) * Real.log (1 + 2 / M) ∧
      (5 / 2) * (M + 3) * Real.log (1 + 2 / M) ≤ 5 + 10 / M := by
  have hm : 0 < M := by linarith
  have hc : 0 ≤ (5 / 2 : ℝ) * (M + 3) := by positivity
  have hl := mul_le_mul_of_nonneg_left
    (logShift_log_one_add_lower (by positivity : 0 ≤ 2 / M)) hc
  have hu := mul_le_mul_of_nonneg_left
    (logShift_log_one_add_upper (by positivity : 0 ≤ 2 / M)) hc
  have heql : (5 / 2 : ℝ) * (M + 3) * (2 / M - (2 / M) ^ 2 / 2) =
      5 + 10 / M - 15 / M ^ 2 := by
    field_simp [hm.ne']
    ring
  have hequ : (5 / 2 : ℝ) * (M + 3) *
      (2 / M - (2 / M) ^ 2 / 2 + (2 / M) ^ 3 / 3) =
        5 + 10 / M + (20 - (25 / 3 : ℝ) * M) / M ^ 3 := by
    field_simp [hm.ne']
    ring
  rw [heql] at hl
  rw [hequ] at hu
  have hr : (20 - (25 / 3 : ℝ) * M) / M ^ 3 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  exact ⟨hl, by linarith⟩

/-- Note Lemma 3.9(c), transport of the exact Lemma 3.9(b) interval. -/
theorem logShift_scaled_amplitude_bounds {M A : ℝ} (hM : 8 ≤ M)
    (hAl : (13 / 20 : ℝ) / (M + 2) ≤ A)
    (hAu : A ≤ 3 / (4 * (M + 2)) + (11 / 10 : ℝ) / (M + 2) ^ 2) :
    (13 / 20 : ℝ) ≤ (M + 3) * A ∧
      (M + 3) * A ≤ 3 / 4 + (49 / 25 : ℝ) / (M + 2) := by
  have hm2 : 0 < M + 2 := by linarith
  have hm3 : 0 < M + 3 := by linarith
  have hn : 10 ≤ M + 2 := by linarith
  constructor
  · have hbase : (13 / 20 : ℝ) = (M + 2) * ((13 / 20 : ℝ) / (M + 2)) := by
      field_simp [hm2.ne']
    calc
      (13 / 20 : ℝ) = (M + 2) * ((13 / 20 : ℝ) / (M + 2)) := hbase
      _ ≤ (M + 3) * ((13 / 20 : ℝ) / (M + 2)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (M + 3) * A := mul_le_mul_of_nonneg_left hAl hm3.le
  · have hu := mul_le_mul_of_nonneg_left hAu hm3.le
    have heq : (M + 3) * (3 / (4 * (M + 2)) + (11 / 10 : ℝ) / (M + 2) ^ 2) =
        3 / 4 + (37 / 20 : ℝ) / (M + 2) + (11 / 10 : ℝ) / (M + 2) ^ 2 := by
      field_simp [hm2.ne']
      ring
    have hr : (11 / 10 : ℝ) / (M + 2) ^ 2 ≤ (11 / 100 : ℝ) / (M + 2) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (M + 2) ^ 2) hm2).2
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) hm2.le]
    have heq2 : (49 / 25 : ℝ) / (M + 2) =
        (37 / 20 : ℝ) / (M + 2) + (11 / 100 : ℝ) / (M + 2) := by
      field_simp
      norm_num
    rw [heq] at hu
    rw [heq2]
    linarith

/-- Note Lemma 3.9(c), the exact `3.55` and `3.85` constants transported from
the logarithmic amplitude interval. This is a helper for the four unconditional
parity statements below, rather than an extra hypothesis on the note theorem. -/
theorem logShiftK_bounds {M A : ℝ} (hM : 8 ≤ M)
    (hAl : (13 / 20 : ℝ) / (M + 2) ≤ A)
    (hAu : A ≤ 3 / (4 * (M + 2)) + (11 / 10 : ℝ) / (M + 2) ^ 2) :
    (71 / 20 : ℝ) ≤ logShiftKValue M A ∧
      logShiftKValue M A ≤ (77 / 20 : ℝ) + 10 / M := by
  have hm : 0 < M := by linarith
  have hm2 : 0 < M + 2 := by linarith
  have hm3 : 0 < M + 3 := by linarith
  have hw := logShift_weighted_log_bounds hM
  have ha := logShift_scaled_amplitude_bounds hM hAl hAu
  have heq : logShiftKValue M A =
      (5 / 2 : ℝ) * (M + 3) * Real.log (1 + 2 / M) - 1 / 2 - (M + 3) * A := by
    unfold logShiftKValue
    field_simp [hm3.ne']
  have hsmall : 15 / M ^ 2 ≤ 2 / M := by
    apply (div_le_div_iff₀ (by positivity : 0 < M ^ 2) hm).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hM) hm.le]
  have hsmall2 : (49 / 25 : ℝ) / (M + 2) ≤ 2 / M := by
    apply (div_le_div_iff₀ hm2 hm).2
    linarith
  have hnonneg : (0 : ℝ) ≤ 1 / M := by positivity
  rw [heq]
  simp only [div_eq_mul_inv] at hw ha hsmall hsmall2 hnonneg ⊢
  constructor
  · nlinarith [hw.1, ha.2]
  · nlinarith [hw.2, ha.1]

/-- Note Lemma 3.9(c), all four parity choices with no additional assumptions. -/
theorem logShiftK_four_formula_bounds {M : ℝ} (hM : 8 ≤ M) :
    ((71 / 20 : ℝ) ≤ logShiftKValue M (logShiftUpperEven (M + 2)) ∧
      logShiftKValue M (logShiftUpperEven (M + 2)) ≤ (77 / 20 : ℝ) + 10 / M) ∧
    ((71 / 20 : ℝ) ≤ logShiftKValue M (logShiftUpperOdd (M + 2)) ∧
      logShiftKValue M (logShiftUpperOdd (M + 2)) ≤ (77 / 20 : ℝ) + 10 / M) ∧
    ((71 / 20 : ℝ) ≤ logShiftKValue M (logShiftLowerEven (M + 2)) ∧
      logShiftKValue M (logShiftLowerEven (M + 2)) ≤ (77 / 20 : ℝ) + 10 / M) ∧
    ((71 / 20 : ℝ) ≤ logShiftKValue M (logShiftLowerOdd (M + 2)) ∧
      logShiftKValue M (logShiftLowerOdd (M + 2)) ≤ (77 / 20 : ℝ) + 10 / M) := by
  rcases logShift_four_formula_bounds (by linarith : 10 ≤ M + 2) with
    ⟨huE, huO, hlE, hlO⟩
  exact ⟨logShiftK_bounds hM huE.1 huE.2, logShiftK_bounds hM huO.1 huO.2,
    logShiftK_bounds hM hlE.1 hlE.2, logShiftK_bounds hM hlO.1 hlO.2⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.logShiftKValue
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftKValue
#check Erdos993Lean.Analytic.V22.Analysis.logShift_weighted_log_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_weighted_log_bounds
#check Erdos993Lean.Analytic.V22.Analysis.logShift_scaled_amplitude_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShift_scaled_amplitude_bounds
#check Erdos993Lean.Analytic.V22.Analysis.logShiftK_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftK_bounds
#check Erdos993Lean.Analytic.V22.Analysis.logShiftK_four_formula_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.logShiftK_four_formula_bounds
