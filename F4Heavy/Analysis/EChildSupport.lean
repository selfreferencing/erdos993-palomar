module

public import F4Heavy.Analysis.EChildCurvature
public import F4Heavy.Analysis.ParametricSupport

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_child_corrected_slope_monotone (e qb : ℝ) (he : 0 < e)
    (hqb : qb ≤ (8/13 : ℝ))
    (hT : ∀ x, 0 < x → x ≤ qb → -(1/8 : ℝ) ≤ childCurveT e x) :
    MonotoneOn (fun x => childCurveV e x+(3/2 : ℝ)*childH x) (Set.Ioc 0 qb) := by
  have hd : ∀ x ∈ Set.Ioc 0 qb,
      DifferentiableAt ℝ (fun y => childCurveV e y+(3/2 : ℝ)*childH y) x := by
    intro x hx
    have hx1 : x < 1 := by linarith [hx.2]
    exact ((childCurveV_derivative e x he hx.1 hx1).add
      ((childH_derivative x hx.1 hx1).const_mul (3/2))).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 qb)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact (e_child_corrected_slope_derivative_positive e x he hx'.1
      (hx'.2.trans hqb) (hT x hx'.1 hx'.2)).le

theorem e_child_quadratic_support (e qb u c : ℝ) (he : 0 < e)
    (hqb : qb ≤ (8/13 : ℝ)) (hu0 : 0 < u) (huq : u ≤ qb)
    (hc0 : 0 < c) (hcq : c ≤ qb)
    (hT : ∀ x, 0 < x → x ≤ qb → -(1/8 : ℝ) ≤ childCurveT e x) :
    childJ e u ≤ childJ e c+childCurveV e c*(childH u-childH c)-
      (3/4 : ℝ)*(childH u-childH c)^2 := by
  have h := parametric_quadratic_support (convex_Ioc (0 : ℝ) qb)
    childH (childJ e) (childCurveV e) (fun x => -childCurveW x/((1-x)*phi x))
    (3/2) u c ⟨hu0, huq⟩ ⟨hc0, hcq⟩
    (fun x hx => childH_derivative x hx.1 (by linarith [hx.2]))
    (fun x hx => childJ_derivative e x he hx.1 (by linarith [hx.2]))
    (fun x hx => (div_neg_of_neg_of_pos
      (neg_neg_of_pos (child_w_bounds x hx.1 (by linarith [hx.2])).1)
      (mul_pos (by linarith [hx.2]) (phi_positive x hx.1 (by linarith [hx.2])))).le)
    (e_child_corrected_slope_monotone e qb he hqb hT)
  norm_num only at h
  exact h

theorem e_child_line_of_contact (e qb u contact s c : ℝ) (he : 0 < e)
    (hqb : qb ≤ (8/13 : ℝ)) (hu0 : 0 ≤ u) (huq : u ≤ qb)
    (hc0 : 0 < contact) (hcq : contact ≤ qb)
    (hT : ∀ x, 0 < x → x ≤ qb → -(1/8 : ℝ) ≤ childCurveT e x)
    (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+(childCurveV e contact-s)^2/3 ≤ c) :
    childJ e u ≤ s*childH u+c := by
  by_cases hu : u = 0
  · simpa [hu, childJ, childH] using hzero
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    have hquad := e_child_quadratic_support e qb u contact he hqb hup huq hc0 hcq hT
    apply quadratic_support_line (childJ e u) (childH u) (childJ e contact)
      (childH contact) (childCurveV e contact) (3/2) s c (by norm_num)
    · norm_num
      exact hquad
    · norm_num
      exact hcontact

theorem e1_child_line_of_contact (e u contact s c : ℝ) (he : (13/10 : ℝ) ≤ e)
    (hu0 : 0 ≤ u) (huq : u ≤ (29/49 : ℝ))
    (hc0 : 0 < contact) (hcq : contact ≤ (29/49 : ℝ))
    (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+(childCurveV e contact-s)^2/3 ≤ c) :
    childJ e u ≤ s*childH u+c :=
  e_child_line_of_contact e (29/49) u contact s c (by linarith) (by norm_num)
    hu0 huq hc0 hcq (fun x hx0 hxq => (e1_child_log_lower e x he hx0 hxq).le) hzero hcontact

theorem e2_child_line_of_contact (e u contact s c : ℝ) (he : (29/20 : ℝ) ≤ e)
    (hu0 : 0 ≤ u) (huq : u ≤ (8/13 : ℝ))
    (hc0 : 0 < contact) (hcq : contact ≤ (8/13 : ℝ))
    (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+(childCurveV e contact-s)^2/3 ≤ c) :
    childJ e u ≤ s*childH u+c :=
  e_child_line_of_contact e (8/13) u contact s c (by linarith) (le_refl _)
    hu0 huq hc0 hcq (fun x hx0 hxq => (e2_child_log_lower e x he hx0 hxq).le) hzero hcontact

end F4Heavy.Analysis
