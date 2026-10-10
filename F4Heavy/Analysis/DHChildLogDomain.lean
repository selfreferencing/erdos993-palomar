module

public import F4Heavy.Analysis.ChildCurve

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem d_child_log_lower (e u : ℝ) (he : (4/5 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (13/23 : ℝ)) :
    -(1/2 : ℝ) < childCurveT e u := by
  have hz : (8/13 : ℝ) ≤ e*(1-u)/u := by
    apply (le_div_iff₀ hu0).mpr
    have hm := mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1-u by linarith)
    nlinarith only [hm, huq]
  have hl := Real.log_le_log (by norm_num : (0 : ℝ) < 8/13) hz
  have hu := negative_log_rational_upper (8/13) (by norm_num)
  have hb : negativeLogUpper (8/13) < (1/2 : ℝ) := by
    norm_num [negativeLogUpper, rationalLog]
  dsimp only [childCurveT]
  linarith only [hl, hu, hb]

theorem h_child_log_lower (e u : ℝ) (he : (7/4 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (7/10 : ℝ)) :
    -(1/3 : ℝ) ≤ childCurveT e u := by
  have hz : (3/4 : ℝ) ≤ e*(1-u)/u := by
    apply (le_div_iff₀ hu0).mpr
    have hm := mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1-u by linarith)
    nlinarith only [hm, huq]
  have hz0 : 0 < e*(1-u)/u := lt_of_lt_of_le (by norm_num) hz
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hz0)
  rw [Real.log_inv] at hl
  have hi : (e*(1-u)/u)⁻¹ ≤ (4/3 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hz0).mpr
    linarith only [hz]
  dsimp only [childCurveT]
  linarith only [hl, hi]

end F4Heavy.Analysis
