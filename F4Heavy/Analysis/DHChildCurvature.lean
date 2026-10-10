module

public import F4Heavy.Analysis.ChildCurvature
public import F4Heavy.Analysis.DHChildLogDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_child_curvature_rational_identity (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    childCurvatureRational (1/2) u = 4*(u^2-5*u+3)/(3*u) := by
  dsimp [childCurvatureRational, childMassUpper]
  field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1),
    ne_of_gt (show 0 < 2-u by linarith)]
  ring

theorem h_child_curvature_rational_identity (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    childCurvatureRational (1/3) u = 4*(2*u^3-16*u^2+35*u-18)/(9*u*(u-2)) := by
  dsimp [childCurvatureRational, childMassUpper]
  field_simp [ne_of_gt hu0, ne_of_gt (sub_pos.mpr hu1),
    ne_of_gt (show 0 < 2-u by linarith), ne_of_lt (show u-2 < 0 by linarith)]
  ring

theorem d_child_curvature_rational_lower (u : ℝ) (hu0 : 0 < u) (huq : u ≤ (13/23 : ℝ)) :
    1 < childCurvatureRational (1/2) u := by
  rw [d_child_curvature_rational_identity u hu0 (by linarith)]
  have hv : 0 ≤ (13/23 : ℝ)-u := sub_nonneg.mpr huq
  have hid : 4*u^2-23*u+12 = 4*((13/23)-u)^2+(425/23)*((13/23)-u)+147/529 := by ring
  have hp : 0 < 4*u^2-23*u+12 := by rw [hid]; positivity
  apply (lt_div_iff₀ (show 0 < 3*u by positivity)).mpr
  nlinarith only [hp]

theorem h_child_curvature_rational_lower (u : ℝ) (hu0 : 0 < u) (huq : u ≤ (7/10 : ℝ)) :
    (1/4 : ℝ) < childCurvatureRational (1/3) u := by
  rw [h_child_curvature_rational_identity u hu0 (by linarith)]
  have hv : 0 ≤ (7/10 : ℝ)-u := sub_nonneg.mpr huq
  have hid : 288-578*u+265*u^2-32*u^3 =
      1137/500+(6351/25)*((7/10)-u)+(989/5)*((7/10)-u)^2+32*((7/10)-u)^3 := by ring
  have hp : 0 < 288-578*u+265*u^2-32*u^3 := by rw [hid]; positivity
  apply (lt_div_iff_of_neg (show 9*u*(u-2) < 0 from
    mul_neg_of_pos_of_neg (by positivity) (by linarith))).mpr
  nlinarith only [hp]

theorem d_child_corrected_slope_derivative_positive (e u : ℝ) (he : (4/5 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (13/23 : ℝ)) :
    0 < deriv (fun x => childCurveV e x+childH x) u := by
  have hn := child_curvature_numerator (1/2) 1 u (childCurveT e u)
    (by norm_num) (by norm_num) hu0 (by linarith) (d_child_log_lower e u he hu0 huq).le
    (d_child_curvature_rational_lower u hu0 huq)
  simpa only [one_mul] using child_corrected_slope_derivative_positive e 1 u
    (by linarith) hu0 (by linarith) hn

theorem h_child_corrected_slope_derivative_positive (e u : ℝ) (he : (7/4 : ℝ) ≤ e)
    (hu0 : 0 < u) (huq : u ≤ (7/10 : ℝ)) :
    0 < deriv (fun x => childCurveV e x+(1/4 : ℝ)*childH x) u := by
  have hn := child_curvature_numerator (1/3) (1/4) u (childCurveT e u)
    (by norm_num) (by norm_num) hu0 (by linarith) (h_child_log_lower e u he hu0 huq)
    (h_child_curvature_rational_lower u hu0 huq)
  exact child_corrected_slope_derivative_positive e (1/4) u (by linarith) hu0 (by linarith) hn

end F4Heavy.Analysis
