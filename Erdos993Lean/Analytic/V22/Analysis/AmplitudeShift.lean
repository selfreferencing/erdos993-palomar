module

public import Erdos993Lean.Analytic.V22.Analysis.Amplitudes

/-!
# Version 2.2 of the manuscript: the template amplitude normalization

Source: note Lemma 3.9(a,c). All divisions and real powers use their source
positive domains. The native upper and lower amplitudes feed the exact
activity-one log-ratio and are not additional hypotheses on the final theorem.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

/-- Source: note Lemma 3.9, `P_X^T`, with retained `X_N`. -/
noncomputable def shapeTemplatePrefactor (mu N X : ℝ) : ℝ :=
  mu ^ (3 / 2 : ℝ) * X / (2 * gaussianA * (N - 1))

/-- Source: note Lemma 3.9, `lambda_X^T`, with `B=N/mu` and `rho=N/(N+1)`. -/
noncomputable def shapeTemplateLambda (mu N X : ℝ) : ℝ :=
  Real.log ((N / mu) * Real.exp ((N / (N + 1)) / 2) /
    shapeTemplatePrefactor mu N X)

theorem shapeGaussianA_pos : 0 < gaussianA := by
  unfold gaussianA
  positivity

theorem shapeTemplatePrefactor_pos {mu N X : ℝ} (hmu : 0 < mu) (hN : 1 < N)
    (hX : 0 < X) : 0 < shapeTemplatePrefactor mu N X := by
  have hg : 0 < gaussianA := shapeGaussianA_pos
  have hNm1 : 0 < N - 1 := by linarith
  unfold shapeTemplatePrefactor
  positivity

/-- Source: note Lemma 3.9(a), the exact prefactor normalization. -/
theorem shapeTemplatePrefactor_normalization {mu N X : ℝ} (hmu : 0 < mu)
    (hN : 1 < N) (hX : 0 < X) :
    shapeTemplatePrefactor mu N X =
      Real.exp (1 / 2 : ℝ) * (N / mu) ^ (-(3 / 2 : ℝ)) * shapeAmplitude N X := by
  have hN0 : 0 < N := by linarith
  have hNm1 : 0 < N - 1 := by linarith
  have hA : 0 < shapeAmplitude N X := shapeAmplitude_pos hN hX
  have hB : 0 < N / mu := div_pos hN0 hmu
  have hR : 0 < Real.exp (1 / 2 : ℝ) * (N / mu) ^ (-(3 / 2 : ℝ)) *
      shapeAmplitude N X :=
    mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hB _)) hA
  apply Real.log_injOn_pos (shapeTemplatePrefactor_pos hmu hN hX) hR
  unfold shapeTemplatePrefactor shapeAmplitude gaussianA
  simp (disch := first | positivity | norm_num | assumption) only [Real.log_div, Real.log_mul, Real.log_exp,
    Real.log_rpow, Real.log_sqrt]
  ring

/-- Source: note Lemma 3.9(a), its exact log-ratio expression. -/
theorem shapeTemplateLambda_eq {mu N X : ℝ} (hmu : 0 < mu) (hN : 1 < N)
    (hX : 0 < X) :
    shapeTemplateLambda mu N X = (5 / 2 : ℝ) * Real.log (N / mu) -
      1 / (2 * (N + 1)) - Real.log (shapeAmplitude N X) := by
  have hN0 : 0 < N := by linarith
  have hN1 : 0 < N + 1 := by linarith
  have hA : 0 < shapeAmplitude N X := shapeAmplitude_pos hN hX
  have hB : 0 < N / mu := div_pos hN0 hmu
  unfold shapeTemplateLambda
  rw [shapeTemplatePrefactor_normalization hmu hN hX]
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_exp, Real.log_rpow]
  have hcorrection : (N / (N + 1)) / 2 - 1 / 2 = -(1 / (2 * (N + 1))) := by
    field_simp [hN1.ne']
    ring
  linarith

/-- Source: note Lemma 3.9(a), `lambda_X^T=lambda_t+k_X/(M+3)` for every
positive `M`; the note's stated natural-number domain `M≥1` is included. -/
theorem shapeTemplateLambda_shift {mu M X : ℝ} (hmu : 0 < mu) (hM : 0 < M)
    (hX : 0 < X) :
    shapeTemplateLambda mu (M + 2) X = (5 / 2 : ℝ) * Real.log (M / mu) +
      logShiftKValue M (Real.log (shapeAmplitude (M + 2) X)) / (M + 3) := by
  have hM2 : 1 < M + 2 := by linarith
  have hM3 : 0 < M + 3 := by linarith
  have hx : 0 < 1 + 2 / M := by positivity
  have hlog : Real.log ((M + 2) / mu) = Real.log (M / mu) + Real.log (1 + 2 / M) := by
    rw [← Real.log_mul (div_pos hM hmu).ne' hx.ne']
    congr 1
    field_simp [hM.ne', hmu.ne']
  rw [shapeTemplateLambda_eq hmu hM2 hX, hlog]
  unfold logShiftKValue
  field_simp [hM3.ne']
  ring

/-- Source: note Lemma 3.9(c), the native upper and lower `k_X` bounds. -/
theorem amplitude_k_bounds {M : ℕ} (hM : 8 ≤ M) :
    ((71 / 20 : ℝ) ≤ logShiftKValue (M : ℝ) (Real.log (upperAmplitude (M + 2))) ∧
      logShiftKValue (M : ℝ) (Real.log (upperAmplitude (M + 2))) ≤
        (77 / 20 : ℝ) + 10 / (M : ℝ)) ∧
    ((71 / 20 : ℝ) ≤ logShiftKValue (M : ℝ) (Real.log (lowerAmplitude (M + 2))) ∧
      logShiftKValue (M : ℝ) (Real.log (lowerAmplitude (M + 2))) ≤
        (77 / 20 : ℝ) + 10 / (M : ℝ)) := by
  have hMr : (8 : ℝ) ≤ M := by exact_mod_cast hM
  have hb := amplitude_log_bounds (N := M + 2) (by omega)
  constructor
  · apply logShiftK_bounds hMr
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.1.1
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.1.2
  · apply logShiftK_bounds hMr
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.2.1
    · simpa only [Nat.cast_add, Nat.cast_ofNat] using hb.2.2

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor
#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda
#check Erdos993Lean.Analytic.V22.Analysis.shapeGaussianA_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeGaussianA_pos
#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor_pos
#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor_normalization
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplatePrefactor_normalization
#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda_eq
#check Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda_shift
#print axioms Erdos993Lean.Analytic.V22.Analysis.shapeTemplateLambda_shift
#check Erdos993Lean.Analytic.V22.Analysis.amplitude_k_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.amplitude_k_bounds
