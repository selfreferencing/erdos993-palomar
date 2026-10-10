module

public import F4Heavy.Analysis.ChildSupport
public import F4Heavy.Analysis.DHChildCurvature

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_child_line_of_contact (e u contact s c : ℝ) (he : (4/5 : ℝ) ≤ e)
    (hu0 : 0 ≤ u) (huq : u ≤ (13/23 : ℝ))
    (hc0 : 0 < contact) (hcq : contact ≤ (13/23 : ℝ)) (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+(childCurveV e contact-s)^2/2 ≤ c) :
    childJ e u ≤ s*childH u+c := by
  refine child_line_of_contact e 1 (13/23) u contact s c (by linarith) (by norm_num)
    (by norm_num) hu0 huq hc0 hcq ?_ hzero ?_
  · intro x hx0 hxq
    simpa only [one_mul] using (d_child_corrected_slope_derivative_positive e x he hx0 hxq).le
  · simpa only [mul_one] using hcontact

theorem h_child_line_of_contact (e u contact s c : ℝ) (he : (7/4 : ℝ) ≤ e)
    (hu0 : 0 ≤ u) (huq : u ≤ (7/10 : ℝ))
    (hc0 : 0 < contact) (hcq : contact ≤ (7/10 : ℝ)) (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+2*(childCurveV e contact-s)^2 ≤ c) :
    childJ e u ≤ s*childH u+c := by
  refine child_line_of_contact e (1/4) (7/10) u contact s c (by linarith) (by norm_num)
    (by norm_num) hu0 huq hc0 hcq ?_ hzero ?_
  · intro x hx0 hxq
    exact (h_child_corrected_slope_derivative_positive e x he hx0 hxq).le
  · convert hcontact using 1 <;> ring

end F4Heavy.Analysis
