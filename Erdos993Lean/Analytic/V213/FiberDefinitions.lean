module

public import Erdos993Lean.Analytic.V213.ZeroTilt

/-!
Source definitions for Section 6.2.
All binomial masses and the weighted valley kernel use the accepted common
definitions. The original probability remains explicit under reflection.
No generated DF10 family is imported or consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def fiberAG : ℝ := (Real.sqrt (2 * Real.pi * Real.exp 1))⁻¹

def fiberSkew (q : ℝ) : ℝ := 2 * q - 1

def fiberVariance (q : ℝ) : ℝ := q * (1 - q)

def fiberWeightL (q : ℝ) : ℝ := q ^ 2 * (3 - 4 * q)

def fiberWeightR (q : ℝ) : ℝ := (1 - q) ^ 2 * (4 * q - 1)

noncomputable def fiberOffset (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  (j : ℝ) - q * M - fiberSkew q / 2

noncomputable def fiberNormalization (q mu : ℝ) : ℝ :=
  Real.rpow mu (3 / 2) / (4 * fiberAG * Real.sqrt (fiberVariance q))

noncomputable def fiberScale (q mu : ℝ) : ℝ := (fiberNormalization q mu)⁻¹

noncomputable def fiberF (q mu : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  fiberNormalization q mu * kernel2 q (fiberWeightL q) (fiberWeightR q) M j +
    fiberOffset q M j ^ 2 / (fiberVariance q * mu)

noncomputable def fiberPsi (t : ℝ) : ℝ := t - 9 / 2 * (t - 1) ^ 2

theorem fiber_variance_skew (q : ℝ) : 1 - fiberSkew q ^ 2 = 4 * fiberVariance q := by
  unfold fiberSkew fiberVariance
  ring

theorem fiber_AG_pos : 0 < fiberAG := by
  unfold fiberAG
  positivity

theorem fiber_variance_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < fiberVariance q := by
  exact mul_pos hq0 (sub_pos.mpr hq1)

theorem fiber_normalization_pos {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) : 0 < fiberNormalization q mu := by
  unfold fiberNormalization
  exact div_pos (Real.rpow_pos_of_pos hmu _) (by
    have := fiber_AG_pos
    have := Real.sqrt_pos.2 (fiber_variance_pos hq0 hq1)
    positivity)

theorem fiber_scale_pos {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) :
    0 < fiberScale q mu := inv_pos.mpr (fiber_normalization_pos hq0 hq1 hmu)

theorem fiber_weights_nonneg {q : ℝ} (hq : q ∈ Set.Icc (1 / 4) (3 / 4)) :
    0 ≤ fiberWeightL q ∧ 0 ≤ fiberWeightR q := by
  constructor
  · exact mul_nonneg (sq_nonneg _) (by linarith [hq.2])
  · exact mul_nonneg (sq_nonneg _) (by linarith [hq.1])

end Erdos993Lean.Analytic.V213
