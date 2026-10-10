module

public import Erdos993Lean.Analytic.V213.FiberMassConsumers

/-!
Eq75 and its printed AM--GM replacement. The named gains retain the
literal central-amplitude shift, actual E_W and H_N*xi^2 term. The general
consumer retains exactly the source guards. The concrete used-window
consumer discharges support, denominators and absorption analytically.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberLowerMassWeight (q mu : ℝ) (M : ℕ) (j : ℤ) (W : ℝ) : ℝ :=
  ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
    Real.exp (Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) *
      (1 - fiberSquareOffset q M j) / 2 -
      ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
      fiberMassError ((M : ℝ) + 2) (fiberSkew q) W) *
    (1 - fiberSquareOffset q M j +
      (((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2)) *
        (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2)

noncomputable def fiberLowerMassGain (q mu : ℝ) (M : ℕ) (j : ℤ) (W : ℝ) : ℝ :=
  fiberSquareOffset q M j + fiberLowerMassWeight q mu M j W *
    Real.exp (-(2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) *
      Real.sqrt (((M : ℝ) + 2) * fiberSquareOffset q M j) +
      2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) / ((M : ℝ) + 3))

noncomputable def fiberLowerMassLinearGain (q mu : ℝ) (M : ℕ) (j : ℤ) (W : ℝ) : ℝ :=
  fiberSquareOffset q M j + fiberLowerMassWeight q mu M j W *
    Real.exp (-((fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) *
      Real.sqrt ((M : ℝ) + 2) * (fiberSquareOffset q M j + W) / Real.sqrt W +
      2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) / ((M : ℝ) + 3))

theorem fiber_mass_linear_correction_le {N xi w W : ℝ}
    (hN : 0 < N) (hxi : 0 ≤ xi) (hw : 0 ≤ w) (hW : 0 < W) :
    (2 * xi * Real.sqrt (N * w) + 2 * xi ^ 2) / (N + 1) ≤
      (xi * Real.sqrt N * (w + W) / Real.sqrt W + 2 * xi ^ 2) / (N + 1) := by
  have h := mul_le_mul_of_nonneg_left (fiber_mass_amgm hw hW)
    (mul_nonneg hxi (Real.sqrt_nonneg N))
  rw [Real.sqrt_mul hN.le] 
  apply div_le_div_of_nonneg_right _ (by positivity)
  convert add_le_add_right h (2 * xi ^ 2) using 1 <;> ring

theorem fiber_mass_linear_gain_le {M : ℕ} {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (hW : 0 < W)
    (j : ℤ) (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberLowerMassLinearGain q mu M j W ≤ fiberLowerMassGain q mu M j W := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hv := fiber_variance_pos hq0' hq1
  have hN : 0 < (M : ℝ) + 2 := by positivity
  have hw0 : 0 ≤ fiberSquareOffset q M j := by
    unfold fiberSquareOffset
    exact div_nonneg (sq_nonneg _) (mul_nonneg hv.le hN.le)
  have hxi : 0 ≤ fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2) := by
    apply div_nonneg _ (Real.sqrt_nonneg _)
    unfold fiberSkew
    linarith
  have hc := fiber_mass_linear_correction_le hN hxi hw0 hW
  have he := Real.exp_le_exp.mpr (neg_le_neg hc)
  have hg : 0 ≤ 1 - fiberSquareOffset q M j +
      (((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2)) *
        (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2 := by
    have hb := fiber_bonus_current_formula hq0' hq1 M
    rw [hb] at hWg
    linarith
  have hp : 0 ≤ fiberLowerMassWeight q mu M j W := by
    unfold fiberLowerMassWeight
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg M) hmu.le) _) (Real.exp_nonneg _)) hg
  unfold fiberLowerMassLinearGain fiberLowerMassGain
  apply add_le_add le_rfl (mul_le_mul_of_nonneg_left _ hp)
  convert he using 1 <;> congr 1 <;> ring

theorem fiber_lower_mass_gain_general {M : ℕ} (hM : 8 ≤ M) {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (hW : 1 ≤ W)
    (j : ℤ) (hJ0 : 0 ≤ j + 1) (hJN : j + 1 ≤ ((M + 2 : ℕ) : ℤ))
    (hLeft : 0 < 1 - (fiberWindowLeft ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hRight : 0 < 1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hAbs : W ≤ 12 * (1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2) /
      ((1 - fiberSkew q ^ 2) * Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)))
    (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberLowerMassGain q mu M j W ≤ fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  simpa only [fiberLowerMassGain, fiberLowerMassWeight] using
    fiber_lower_normalized_general hM hq0 hqh hmu hW j hJ0 hJN hLeft hRight hAbs hw hWg

theorem fiber_lower_mass_linear_gain_general {M : ℕ} (hM : 8 ≤ M) {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (hW : 1 ≤ W)
    (j : ℤ) (hJ0 : 0 ≤ j + 1) (hJN : j + 1 ≤ ((M + 2 : ℕ) : ℤ))
    (hLeft : 0 < 1 - (fiberWindowLeft ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hRight : 0 < 1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2)
    (hAbs : W ≤ 12 * (1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2) /
      ((1 - fiberSkew q ^ 2) * Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)))
    (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberLowerMassLinearGain q mu M j W ≤ fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  exact (fiber_mass_linear_gain_le hq0 hqh hmu (by linarith) j hw hWg).trans
    (fiber_lower_mass_gain_general hM hq0 hqh hmu hW j hJ0 hJN hLeft hRight hAbs hw hWg)

theorem fiber_lower_mass_gain_used_windows {M : ℕ} (hM : 12 ≤ M) {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (hW : 1 ≤ W) (hWh : W ≤ 3 / 2) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberLowerMassGain q mu M j W ≤ fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hg := fiber_mass_used_window_guards hM hq0 hqh hW hWh j hw
  exact fiber_lower_mass_gain_general (by omega) hq0 hqh hmu hW j
    hg.1.1 hg.1.2 hg.2.1 hg.2.2.1 hg.2.2.2 hw hWg

theorem fiber_lower_mass_linear_gain_used_windows {M : ℕ} (hM : 12 ≤ M) {q mu W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu)
    (hW : 1 ≤ W) (hWh : W ≤ 3 / 2) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ W) (hWg : W ≤ fiberBonus q M) :
    fiberLowerMassLinearGain q mu M j W ≤ fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hg := fiber_mass_used_window_guards hM hq0 hqh hW hWh j hw
  exact fiber_lower_mass_linear_gain_general (by omega) hq0 hqh hmu hW j
    hg.1.1 hg.1.2 hg.2.1 hg.2.2.1 hg.2.2.2 hw hWg

end Erdos993Lean.Analytic.V213
