module

public import Erdos993Lean.Analytic.V213.FiberMassDomains

/-!
General conditional Eq73: cubic absorption and the exact mass exponent.
The window W is arbitrary with W>=1; positive displayed denominators and
its printed absorption inequality are retained. This proof adapts the
algebra/integration organization of the earlier GaussianLower
source, generalizing its old W=1 proof rather than importing that restricted
statement as the current theorem. No finite data is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set Erdos993Lean.Analytic.V22.Analysis

theorem fiber_quartic_ratio_mono {z Z A D : ℝ} (hA : 0 ≤ A)
    (hD : 0 < D) (hz : |z| ≤ Z) :
    A * z ^ 4 / (12 * D) ≤ A * Z ^ 4 / (12 * D) := by
  have hp := pow_le_pow_left₀ (abs_nonneg z) hz 4
  rw [(by decide : Even 4).pow_abs z] at hp
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hA) (by positivity)

theorem fiber_right_cubic_absorption {r N W u : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hN : 0 < N)
    (hRight : 0 < 1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2)
    (hAbs : W * (1 - r ^ 2) * N ≤
      12 * (N + 1) * (1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2))
    (hu : r ≤ u) (huw : u ^ 2 ≤ W * Erdos993Lean.Analytic.V22.varianceR r * N) :
    (N + 1) * r * (sharedGaussianZ r N u) ^ 3 /
        (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2))) ≤
      2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
  have hn0 : 0 < N := hN
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hu0 : 0 ≤ u := le_trans hr0 hu
  let DR : ℝ := 1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2
  let D : ℝ := DR * (1 - r ^ 2)
  have hDR : 0 < DR := hRight
  have hvr : 1 - r ^ 2 = 4 * Erdos993Lean.Analytic.V22.varianceR r := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    ring
  have hD : 0 < D := by dsimp [D]; rw [hvr]; positivity
  have hz0 : 0 ≤ sharedGaussianZ r N u := by
    unfold sharedGaussianZ
    exact div_nonneg (by linarith) hn1.le
  have hzu : sharedGaussianZ r N u ≤ 2 * u / (N + 1) := by
    unfold sharedGaussianZ
    exact div_le_div_of_nonneg_right (by linarith) hn1.le
  have hz3 := pow_le_pow_left₀ hz0 hzu 3
  have hcube := mul_le_mul_of_nonneg_left hz3
    (show 0 ≤ (N + 1) * r / (3 * D) by positivity)
  have hcubic : (N + 1) * r * (sharedGaussianZ r N u) ^ 3 / (3 * D) ≤
      8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) := by
    convert hcube using 1 <;> field_simp [hn1.ne', hD.ne'] <;> ring
  have hu2 : u ^ 2 ≤ 3 * (N + 1) * DR := by
    have hscaled : W * Erdos993Lean.Analytic.V22.varianceR r * N ≤ 3 * (N + 1) * DR := by
      change W * (1 - r ^ 2) * N ≤ 12 * (N + 1) * DR at hAbs
      rw [hvr] at hAbs
      nlinarith
    exact huw.trans hscaled
  have hmul := mul_le_mul_of_nonneg_left hu2
    (show 0 ≤ 8 * r * u * Erdos993Lean.Analytic.V22.varianceR r * (N + 1) by positivity)
  have hfinal : 8 * r * u ^ 3 / (3 * (N + 1) ^ 2 * D) ≤
      2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 3 * (N + 1) ^ 2 * D)
      (by positivity : 0 < Erdos993Lean.Analytic.V22.varianceR r * (N + 1))).2
    dsimp [D]
    rw [hvr]
    convert hmul using 1 <;> ring
  exact hcubic.trans hfinal

theorem fiber_mass_exponent_upper {r N W : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (hN : 0 < N) (hW : 1 ≤ W)
    (hLeft : 0 < 1 - (Erdos993Lean.Analytic.V22.ZL r N W) ^ 2)
    (hRight : 0 < 1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2)
    (hAbs : W * (1 - r ^ 2) * N ≤
      12 * (N + 1) * (1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2))
    (x : ℝ) (hw : x ^ 2 ≤ W) :
    (N + 1) * sharedKLPsi r (sharedGaussianZ r N (Erdos993Lean.Analytic.V22.sN r N * x)) ≤
      Erdos993Lean.Analytic.V22.rho N / 2 * x ^ 2 +
        Erdos993Lean.Analytic.V22.epsilon r N * |x| +
        Erdos993Lean.Analytic.V22.c0 r N + Erdos993Lean.Analytic.V22.quarticError r N W := by
  have hn0 : 0 < N := hN
  have hn1 : 0 < N + 1 := by linarith
  have hv := shared_varianceR_pos hr0 hr1
  have hvr := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs := shared_sN_sq hr0 hr1 hn0
  have hs0 : 0 ≤ Erdos993Lean.Analytic.V22.sN r N := Real.sqrt_nonneg _
  let u : ℝ := Erdos993Lean.Analytic.V22.sN r N * x
  let z : ℝ := sharedGaussianZ r N u
  have hW0 : 0 < W := by linarith
  have hu2 : u ^ 2 ≤ W * Erdos993Lean.Analytic.V22.varianceR r * N := by
    have hh := mul_le_mul_of_nonneg_left hw (sq_nonneg (Erdos993Lean.Analytic.V22.sN r N))
    dsimp [u]
    simpa only [mul_pow, hs, mul_assoc, mul_comm, mul_left_comm] using hh
  have huabs : |u| ≤ Real.sqrt W * Erdos993Lean.Analytic.V22.sN r N := by
    apply abs_le_of_sq_le_sq ?_ (by positivity)
    simpa only [u, mul_pow, Real.sq_sqrt hW0.le, hs, mul_assoc] using hu2
  obtain ⟨huL, huR⟩ := abs_le.mp huabs
  have hZR0 : 0 < Erdos993Lean.Analytic.V22.ZR r N W := by
    unfold Erdos993Lean.Analytic.V22.ZR Erdos993Lean.Analytic.V22.sN
    positivity
  have hZL0 : 0 < Erdos993Lean.Analytic.V22.ZL r N W := by
    unfold Erdos993Lean.Analytic.V22.ZL Erdos993Lean.Analytic.V22.sN
    positivity
  have hZL1 : Erdos993Lean.Analytic.V22.ZL r N W < 1 := by nlinarith
  have hrZR : r + Erdos993Lean.Analytic.V22.ZR r N W < 1 := by nlinarith
  have hDL : 0 < (1 - (Erdos993Lean.Analytic.V22.ZL r N W) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < Erdos993Lean.Analytic.V22.ZL r N W) hZL1) hvr
  have hDR : 0 < (1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2) :=
    mul_pos (shared_one_sub_sq_pos (by linarith : -1 < r + Erdos993Lean.Analytic.V22.ZR r N W) hrZR) hvr
  have hquad := shared_lower_exponent_identity hr0 hr1 hn0 x
  have heps := shared_epsilon_nonneg hr0 hr1 hn0
  by_cases hleft : u ≤ r
  · have hz0 : z ≤ 0 := by dsimp [z, sharedGaussianZ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hn1.le
    have hzL : -Erdos993Lean.Analytic.V22.ZL r N W ≤ z := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZL
      rw [← neg_div]
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_left hr0 hr1 hZL0 hZL1 hzL hz0) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N W) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N W := by
      unfold Erdos993Lean.Analytic.V22.quarticError
      apply le_trans ?_ (le_max_left _ _)
      have h := fiber_quartic_ratio_mono (z := z)
        (Z := Erdos993Lean.Analytic.V22.ZL r N W) hn1.le hDL
        (by rw [abs_of_nonpos hz0]; linarith)
      simpa only [mul_assoc] using h
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (Erdos993Lean.Analytic.V22.ZL r N W) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (neg_le_abs x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    linarith
  · have hu : r ≤ u := by linarith
    have hz0 : 0 ≤ z := by dsimp [z, sharedGaussianZ]; exact div_nonneg (by linarith) hn1.le
    have hzR : z ≤ Erdos993Lean.Analytic.V22.ZR r N W := by
      dsimp [z, sharedGaussianZ]
      unfold Erdos993Lean.Analytic.V22.ZR
      exact div_le_div_of_nonneg_right (by linarith) hn1.le
    have hgauss := mul_le_mul_of_nonneg_left
      (sharedKLPsi_gaussian_right hr0 hr1 hZR0 hrZR hz0 hzR) hn1.le
    have hquartic : (N + 1) * z ^ 4 /
        (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2))) ≤
        Erdos993Lean.Analytic.V22.quarticError r N W := by
      unfold Erdos993Lean.Analytic.V22.quarticError
      apply le_trans ?_ (le_max_right _ _)
      have h := fiber_quartic_ratio_mono (z := z)
        (Z := Erdos993Lean.Analytic.V22.ZR r N W) hn1.le hDR
        (by rw [abs_of_nonneg hz0]; exact hzR)
      simpa only [mul_assoc] using h
    have hcubic := fiber_right_cubic_absorption hr0 hr1 hN hRight hAbs hu hu2
    have hlin : 2 * Erdos993Lean.Analytic.V22.epsilon r N * x =
        2 * r * u / (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
      rw [shared_epsilon_eq hr0 hr1 hn0]
      dsimp [u]
      ring
    rw [← hlin] at hcubic
    have hgauss' : (N + 1) * sharedKLPsi r z ≤
        (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) +
        (N + 1) * r * z ^ 3 /
          (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2))) +
        (N + 1) * z ^ 4 /
          (12 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2))) := by
      convert hgauss using 1 <;> field_simp [hDR.ne'] <;> ring
    change (N + 1) * z ^ 2 / (2 * (1 - r ^ 2)) = _ at hquad
    rw [hquad] at hgauss'
    have habs := mul_le_mul_of_nonneg_left (le_abs_self x) heps
    change (N + 1) * sharedKLPsi r z ≤ _
    change (N + 1) * r * z ^ 3 /
      (3 * ((1 - (r + Erdos993Lean.Analytic.V22.ZR r N W) ^ 2) * (1 - r ^ 2))) ≤
      2 * Erdos993Lean.Analytic.V22.epsilon r N * x at hcubic
    linarith


end Erdos993Lean.Analytic.V213
