module

public import F4Heavy.Analysis.ChildCurve
public import F4Heavy.Analysis.ParametricSupport

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem child_corrected_slope_monotone (e k qb : ℝ) (he : 0 < e) (hqb : qb < 1)
    (hderiv : ∀ x, 0 < x → x ≤ qb →
      0 ≤ deriv (fun y => childCurveV e y+k*childH y) x) :
    MonotoneOn (fun x => childCurveV e x+k*childH x) (Set.Ioc 0 qb) := by
  have hd : ∀ x ∈ Set.Ioc 0 qb,
      DifferentiableAt ℝ (fun y => childCurveV e y+k*childH y) x := by
    intro x hx
    exact ((childCurveV_derivative e x he hx.1 (hx.2.trans_lt hqb)).add
      ((childH_derivative x hx.1 (hx.2.trans_lt hqb)).const_mul k)).differentiableAt
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 qb)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableWithinAt
  · intro x hx
    have hx' := interior_subset hx
    exact hderiv x hx'.1 hx'.2

theorem child_quadratic_support (e k qb u c : ℝ) (he : 0 < e) (hqb : qb < 1)
    (hu0 : 0 < u) (huq : u ≤ qb) (hc0 : 0 < c) (hcq : c ≤ qb)
    (hderiv : ∀ x, 0 < x → x ≤ qb →
      0 ≤ deriv (fun y => childCurveV e y+k*childH y) x) :
    childJ e u ≤ childJ e c+childCurveV e c*(childH u-childH c)-
      k/2*(childH u-childH c)^2 := by
  exact parametric_quadratic_support (convex_Ioc (0 : ℝ) qb)
    childH (childJ e) (childCurveV e) (fun x => -childCurveW x/((1-x)*phi x))
    k u c ⟨hu0, huq⟩ ⟨hc0, hcq⟩
    (fun x hx => childH_derivative x hx.1 (hx.2.trans_lt hqb))
    (fun x hx => childJ_derivative e x he hx.1 (hx.2.trans_lt hqb))
    (fun x hx => (div_neg_of_neg_of_pos
      (neg_neg_of_pos (child_w_bounds x hx.1 (hx.2.trans_lt hqb)).1)
      (mul_pos (sub_pos.mpr (hx.2.trans_lt hqb)) (phi_positive x hx.1 (hx.2.trans_lt hqb)))).le)
    (child_corrected_slope_monotone e k qb he hqb hderiv)

theorem child_line_of_contact (e k qb u contact s c : ℝ) (he : 0 < e)
    (hk : 0 < k) (hqb : qb < 1) (hu0 : 0 ≤ u) (huq : u ≤ qb)
    (hc0 : 0 < contact) (hcq : contact ≤ qb)
    (hderiv : ∀ x, 0 < x → x ≤ qb →
      0 ≤ deriv (fun y => childCurveV e y+k*childH y) x)
    (hzero : 0 ≤ s+c)
    (hcontact : childJ e contact-s*childH contact+(childCurveV e contact-s)^2/(2*k) ≤ c) :
    childJ e u ≤ s*childH u+c := by
  by_cases hu : u = 0
  · simpa [hu, childJ, childH] using hzero
  · have hup : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hu)
    exact quadratic_support_line (childJ e u) (childH u) (childJ e contact)
      (childH contact) (childCurveV e contact) k s c hk
      (child_quadratic_support e k qb u contact he hqb hup huq hc0 hcq hderiv) hcontact

end F4Heavy.Analysis
