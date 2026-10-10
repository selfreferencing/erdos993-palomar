module

public import F4Heavy.Analysis.CapResponseBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_parent_mass_log_upper (lam Y : ℝ) (hlam : 0 < lam)
    (hH : parentH Y ≤ q lam) : Y ≤ Real.log (1 + lam) := by
  have hden : 0 < 1 + lam := by linarith
  have hmul : (1 - Real.exp (-Y)) * (1 + lam) ≤ lam := (le_div_iff₀ hden).mp hH
  have he : Real.exp (-Real.log (1 + lam)) ≤ Real.exp (-Y) := by
    rw [Real.exp_neg, Real.exp_log hden, ← one_div]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hmul]
  have h := Real.exp_le_exp.mp he
  linarith only [h]

theorem cap_log_tangent (t : ℝ) (ht : 0 < t)
    (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) :
    Real.log t < (2 / 5) * t - 1 / 12 := by
  have h := Real.log_le_sub_one_of_pos (div_pos ht (by norm_num : (0 : ℝ) < 5 / 2))
  rw [Real.log_div (ne_of_gt ht) (by norm_num : (5 / 2 : ℝ) ≠ 0)] at h
  linarith only [h, hlog]

theorem cap_parent_mass_affine_upper (lam Y : ℝ) (hlam : 0 < lam)
    (hH : parentH Y ≤ q lam) (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) :
    Y < 19 / 60 + 2 * lam / 5 := by
  have h1 := cap_parent_mass_log_upper lam Y hlam hH
  have h2 := cap_log_tangent (1 + lam) (by linarith) hlog
  linarith only [h1, h2]

theorem cap_exponential_dual_lower (lam G M Y : ℝ) (hl : 0 < lam) (hG : 0 < G)
    (hM : 0 < M) :
    M * (1 - Real.log (lam * M / G)) ≤ G * Real.exp Y / lam - M * Y := by
  have ht : 0 < lam * M / G := div_pos (mul_pos hl hM) hG
  have he := Real.add_one_le_exp (Y - Real.log (lam * M / G))
  rw [Real.exp_sub, Real.exp_log ht] at he
  have hm := mul_le_mul_of_nonneg_left he hM.le
  have hid : M * (Real.exp Y / (lam * M / G)) = G * Real.exp Y / lam := by
    field_simp
  rw [hid] at hm
  linarith only [hm]

theorem cap_exponential_tangent_lower (lam G M Y : ℝ) (hl : 0 < lam) (hG : 0 < G)
    (hM : 0 < M) (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) :
    M * (13 / 12 - 2 * (lam * M / G) / 5) ≤ G * Real.exp Y / lam - M * Y := by
  have h1 := cap_exponential_dual_lower lam G M Y hl hG hM
  have h2 := cap_log_tangent (lam * M / G) (div_pos (mul_pos hl hM) hG) hlog
  have h3 := mul_le_mul_of_nonneg_left
    (show 13 / 12 - 2 * (lam * M / G) / 5 ≤ 1 - Real.log (lam * M / G) by linarith only [h2]) hM.le
  exact h3.trans h1

theorem cap_parent_probability_inverse (lam Y : ℝ) (hlam : 0 < lam) :
    1 / p lam Y = 1 + Real.exp Y / lam := by
  have he := Real.exp_pos Y
  unfold p
  rw [Real.exp_neg]
  field_simp
  <;> ring

theorem cap_response_slope_exp_identity (r : Row) (lam Y rho h : ℝ) (hlam : 0 < lam) :
    (capC r lam Y rho + 2 * capD r lam Y rho * h) / p lam Y =
      2 * (gamma r lam - delta r lam) * h - alpha r lam - beta r lam +
      2 * parentP r lam Y rho * (1 - Y * h) +
      2 * h * ((gamma r lam - delta r lam) * Real.exp Y / lam) := by
  rw [cap_response_slope_identity r lam Y rho h (ne_of_gt (p_pos lam Y hlam))]
  have hi := cap_parent_probability_inverse lam Y hlam
  calc
    _ = 2 * (gamma r lam - delta r lam) * h * (1 / p lam Y) - alpha r lam - beta r lam +
        2 * parentP r lam Y rho * (1 - Y * h) := by ring
    _ = _ := by rw [hi]; ring

end F4Heavy.Analysis
