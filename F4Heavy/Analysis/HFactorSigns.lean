module

public import F4Heavy.Analysis.PolynomialSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem h_denominator_factor_signs (v x : ℝ) (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ))
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < v+1 ∧ 0 < 1-v ∧ 0 < v+11/3 ∧ 0 < x+1 ∧
    0 < v*x+3*v/7+x+11/7 ∧ 0 < (1-v^2)*x+(3*v+11)^2/28 ∧
    0 < x^2+4*x/3+1/9 := by
  have hv0 := hv.1
  have hx0 : 0 < x := by linarith only [hx.1]
  have hv1 : v < 1 := by linarith only [hv.2]
  have hs : 0 < 1-v^2 := by nlinarith only [hv0, hv1, sq_nonneg (1-v)]
  refine ⟨by positivity, by linarith only [hv1], by positivity, by positivity, ?_, ?_, ?_⟩
  · positivity
  · exact add_pos_of_pos_of_nonneg (mul_pos hs hx0) (div_nonneg (sq_nonneg _) (by norm_num))
  · positivity

end F4Heavy.Analysis
