module

public import F4Heavy.Analysis.CapParentBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_c_parabolic_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hrho : FeasibleVacancy lam Y rho) :
    capC r lam Y rho ≤ p lam Y *
      ((2 + 2 * gamma r lam - alpha r lam - beta r lam) - (2 + gamma r lam) * p lam Y) := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hp1 := p_lt_one lam Y hl
  have hP := parentP_linear_upper r lam Y rho hr
  have hv := mul_le_mul_of_nonneg_right hrho.2 (sub_nonneg.mpr hp1.le)
  have h := mul_le_mul_of_nonneg_left
    (show 2 * parentP r lam Y rho - alpha r lam - beta r lam ≤
      (2 + 2 * gamma r lam - alpha r lam - beta r lam) - (2 + gamma r lam) * p lam Y by
      linarith only [hP, hv]) hp.le
  exact h

theorem cap_parabola_decreasing_bound (E g p s : ℝ) (hg : 0 ≤ g)
    (hsp : s ≤ p) (hs : E ≤ 2 * g * s) :
    p * (E - g * p) ≤ s * (E - g * s) := by
  have hfactor : E - g * (p + s) ≤ 0 := by
    have hmul := mul_le_mul_of_nonneg_left hsp hg
    linarith only [hs, hmul]
  have h := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hsp) hfactor
  nlinarith only [h]

theorem cap_parabola_vertex_bound (E g p : ℝ) (hg : 0 < g) :
    p * (E - g * p) ≤ E ^ 2 / (4 * g) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) hg)).mpr
  nlinarith only [sq_nonneg (2 * g * p - E)]

theorem cap_c_vertex_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hrho : FeasibleVacancy lam Y rho) :
    capC r lam Y rho ≤ (2 + 2 * gamma r lam - alpha r lam - beta r lam) ^ 2 /
      (4 * (2 + gamma r lam)) := by
  exact (cap_c_parabolic_upper r lam Y rho hr hrho).trans
    (cap_parabola_vertex_bound _ _ _ (by linarith only [row_gamma_pos r lam hr]))

theorem cap_c_endpoint_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hs : 2 + 2 * gamma r lam - alpha r lam - beta r lam ≤
      2 * (2 + gamma r lam) * (lam / (1 + 2 * lam))) :
    capC r lam Y rho ≤ (lam / (1 + 2 * lam)) *
      ((2 + 2 * gamma r lam - alpha r lam - beta r lam) -
        (2 + gamma r lam) * (lam / (1 + 2 * lam))) := by
  exact (cap_c_parabolic_upper r lam Y rho hr hrho).trans
    (cap_parabola_decreasing_bound _ _ _ _ (by linarith only [row_gamma_pos r lam hr])
      (cap_parent_probability_lower lam Y (inRow_activity_pos r lam hr) hH) hs)

/-- The reserve guard implies the positive numerator for the attained response. -/
theorem cap_response_numerator_of_reserve_bound (c delta h J B C : ℝ)
    (hh : 0 < h) (hJ : 0 ≤ J) (hd : 0 < delta)
    (hc : c ≤ C) (hJB : J ≤ B * h) (hguard : C * B < 2 * delta) :
    0 < 2 * delta * h - c * J := by
  by_cases hc0 : c ≤ 0
  · have hm := mul_nonpos_of_nonpos_of_nonneg hc0 hJ
    have hp := mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hd) hh
    linarith only [hm, hp]
  · have hC : 0 ≤ C := by linarith only [hc, hc0]
    have h1 := mul_le_mul_of_nonneg_right hc hJ
    have h2 := mul_le_mul_of_nonneg_left hJB hC
    have h3 := mul_lt_mul_of_pos_right hguard hh
    nlinarith only [h1, h2, h3]

/-- Exact response-slope identity; no source or parent replacement occurs. -/
theorem cap_response_slope_identity (r : Row) (lam Y rho h : ℝ)
    (hp : p lam Y ≠ 0) :
    (capC r lam Y rho + 2 * capD r lam Y rho * h) / p lam Y =
      2 * (gamma r lam - delta r lam) * h / p lam Y - alpha r lam - beta r lam +
      2 * parentP r lam Y rho * (1 - Y * h) := by
  unfold capC capD
  field_simp
  <;> ring

end F4Heavy.Analysis
