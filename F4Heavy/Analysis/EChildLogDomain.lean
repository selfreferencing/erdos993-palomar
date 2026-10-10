module

public import F4Heavy.Analysis.ChildMass

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem log_lower_eighth_of_ratio (z : ℝ) (hz : (8/9 : ℝ) < z) :
    -(1/8 : ℝ) < Real.log z := by
  have hz0 : 0 < z := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hz0)
  rw [Real.log_inv] at h
  have hi : z⁻¹ < (9/8 : ℝ) := by
    rw [inv_eq_one_div]
    apply (div_lt_iff₀ hz0).mpr
    linarith only [hz]
  linarith only [h, hi]

theorem e1_child_log_lower (e u : ℝ) (he : (13/10 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (29/49 : ℝ)) :
    -(1/8 : ℝ) < Real.log (e*(1-u)/u) := by
  apply log_lower_eighth_of_ratio
  apply (lt_div_iff₀ hu0).mpr
  have hm := mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1-u by linarith)
  nlinarith only [hm, huq]

theorem e2_child_log_lower (e u : ℝ) (he : (29/20 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (8/13 : ℝ)) :
    -(1/8 : ℝ) < Real.log (e*(1-u)/u) := by
  apply log_lower_eighth_of_ratio
  apply (lt_div_iff₀ hu0).mpr
  have hm := mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ 1-u by linarith)
  nlinarith only [hm, huq]

-- The manuscript's shared extended E1 domain cannot use its stated log bound.
-- The two row-specific bounds above suffice for their activity interpolations.
theorem e_shared_extension_log_counterexample :
    Real.log (((13/10 : ℝ)*(1-8/13))/(8/13)) < -(1/8 : ℝ) := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 13/16)
  norm_num at h ⊢
  linarith only [h]

end F4Heavy.Analysis
