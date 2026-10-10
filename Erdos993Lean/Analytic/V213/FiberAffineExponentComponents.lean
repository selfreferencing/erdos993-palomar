module

public import Erdos993Lean.Analytic.V213.FiberAffineScalarCheck
public import Erdos993Lean.Analytic.V213.FiberAffineY

/-!
The F03 squared comparisons imply the printed root bounds on every real
N>=22 or N>=32. The remaining h(N), xi and rho terms are bounded on the
same full domains. These are bindings to actual exponent operands, not
checks of unrelated positive numbers.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_affine_root22 {N : ℝ} (hN : 22 ≤ N) :
    Real.sqrt N / (N + 1) ≤ 47 / 230 := by
  have hs : Real.sqrt (22 : ℝ) / 23 ≤ 47 / 230 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (22 : ℝ) / 23)
      (by norm_num : (0 : ℝ) ≤ 47 / 230)).1
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)]
    exact fiber_affine_root22_squared
  have h := fiber_sqrt_ratio_antitone (by norm_num : (1 : ℝ) ≤ 22) hN
  norm_num only at h
  exact h.trans hs

theorem fiber_affine_root32 {N : ℝ} (hN : 32 ≤ N) :
    Real.sqrt N / (N + 1) ≤ 2 / 11 := by
  have hs : Real.sqrt (32 : ℝ) / 33 ≤ 2 / 11 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (32 : ℝ) / 33)
      (by norm_num : (0 : ℝ) ≤ 2 / 11)).1
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32)]
    exact fiber_affine_root32_squared
  have h := fiber_sqrt_ratio_antitone (by norm_num : (1 : ℝ) ≤ 32) hN
  norm_num only at h
  exact h.trans hs

theorem fiber_affine_inverse_root : 1 / Real.sqrt (3 / 2 : ℝ) ≤ 5 / 6 := by
  have hs : 0 < Real.sqrt (3 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  apply (sq_le_sq₀ (by positivity : 0 ≤ 1 / Real.sqrt (3 / 2 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 5 / 6)).1
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)]
  convert fiber_affine_inverse_root_squared using 1 <;> norm_num

theorem fiber_affine_root_correction22 {N : ℝ} (hN : 22 ≤ N) :
    (4 / 25 : ℝ) * Real.sqrt N / (Real.sqrt (3 / 2) * (N + 1)) ≤ 47 / 1725 := by
  have h := mul_le_mul fiber_affine_inverse_root (fiber_affine_root22 hN)
    (by positivity : 0 ≤ Real.sqrt N / (N + 1)) (by norm_num : (0 : ℝ) ≤ 5 / 6)
  calc
    _ = (4 / 25 : ℝ) * ((1 / Real.sqrt (3 / 2)) * (Real.sqrt N / (N + 1))) := by
      rw [div_mul_eq_div_div]
      ring
    _ ≤ (4 / 25 : ℝ) * ((5 / 6) * (47 / 230)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by norm_num

theorem fiber_affine_root_correction32 {N : ℝ} (hN : 32 ≤ N) :
    (4 / 25 : ℝ) * Real.sqrt N / (Real.sqrt (3 / 2) * (N + 1)) ≤ 4 / 165 := by
  have h := mul_le_mul fiber_affine_inverse_root (fiber_affine_root32 hN)
    (by positivity : 0 ≤ Real.sqrt N / (N + 1)) (by norm_num : (0 : ℝ) ≤ 5 / 6)
  calc
    _ = (4 / 25 : ℝ) * ((1 / Real.sqrt (3 / 2)) * (Real.sqrt N / (N + 1))) := by
      rw [div_mul_eq_div_div]
      ring
    _ ≤ (4 / 25 : ℝ) * ((5 / 6) * (2 / 11)) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = _ := by norm_num

theorem fiber_affine_h22 {N : ℝ} (hN : 22 ≤ N) :
    ((77 / 20 : ℝ) + 10 / (N - 2)) / (N + 1) ≤ 87 / 460 := by
  have hd : 0 < N - 2 := by linarith
  have hm : 0 < N + 1 := by linarith
  have hi : 10 / (N - 2) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hd).2
    linarith only [hN]
  apply (div_le_iff₀ hm).2
  linarith only [hi, hN]

theorem fiber_affine_h32 {N : ℝ} (hN : 32 ≤ N) :
    ((77 / 20 : ℝ) + 10 / (N - 2)) / (N + 1) ≤ 251 / 1980 := by
  have hd : 0 < N - 2 := by linarith
  have hm : 0 < N + 1 := by linarith
  have hi : 10 / (N - 2) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ hd).2
    linarith only [hN]
  apply (div_le_iff₀ hm).2
  linarith only [hi, hN]

theorem fiber_affine_rho_loss {N w : ℝ} (hN : 0 < N) (hw : 0 ≤ w) :
    (1 - w) / 2 - 1 / (2 * (N + 1)) ≤ V22.rho N * (1 - w) / 2 := by
  have hm : 0 < N + 1 := by linarith
  have he : V22.rho N * (1 - w) / 2 - ((1 - w) / 2 - 1 / (2 * (N + 1))) =
      w / (2 * (N + 1)) := by
    unfold V22.rho
    field_simp [hm.ne']
    ring
  have hp : 0 ≤ w / (2 * (N + 1)) := by positivity
  linarith only [he, hp]

end Erdos993Lean.Analytic.V213
