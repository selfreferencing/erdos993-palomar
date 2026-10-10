module

public import F4Heavy.Analysis.PolynomialSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem d_denominator_factor_signs (v x : ℝ) (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ))
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < v+1 ∧ 0 < 1-v ∧ 0 < 9-v ∧ 0 < x+1 ∧
    0 < v*x-v/4+x+9/4 ∧ 0 < (1-v^2)*x+(v-9)^2/20 ∧
    0 < x^2+4*x/3+1/9 := by
  have hx0 : 0 < x := by linarith only [hx.1]
  have hv1 : v < 1 := by linarith only [hv.2]
  have hs : 0 < 1-v^2 := by nlinarith only [hv.1, hv1, sq_nonneg (1-v)]
  refine ⟨by linarith only [hv.1], by linarith only [hv1],
    by linarith only [hv.2], by linarith only [hx0], ?_, ?_, ?_⟩
  · have hm : 0 ≤ v*(x-1/4) := mul_nonneg hv.1 (by linarith only [hx.1])
    nlinarith only [hm, hx0]
  · exact add_pos_of_pos_of_nonneg (mul_pos hs hx0) (div_nonneg (sq_nonneg _) (by norm_num))
  · positivity

end F4Heavy.Analysis
