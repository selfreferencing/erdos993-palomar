module

public import F4Heavy.Analysis.ChildCurve
public import F4Heavy.Analysis.EChildLogDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eChildCurvatureBound (u : ℝ) : ℝ :=
  (u^3-13*u^2+40*u-24)/(3*u*(u-2))

theorem e_child_curvature_rational_lower (u : ℝ) (hu0 : 0 < u) (huq : u ≤ (8/13 : ℝ)) :
    (3/2 : ℝ) < eChildCurvatureBound u := by
  have hv : 0 ≤ (8/13 : ℝ)-u := sub_nonneg.mpr huq
  have hid : 48-98*u+35*u^2-2*u^3 =
      (48-98*(8/13)+35*(8/13)^2-2*(8/13)^3)+
      (98-70*(8/13)+6*(8/13)^2)*((8/13)-u)+
      (35-6*(8/13))*((8/13)-u)^2+2*((8/13)-u)^3 := by ring
  have hp : 0 < 48-98*u+35*u^2-2*u^3 := by
    rw [hid]
    positivity
  unfold eChildCurvatureBound
  apply (lt_div_iff_of_neg (show 3*u*(u-2) < 0 by
    exact mul_neg_of_pos_of_neg (by positivity) (by linarith))).mpr
  nlinarith only [hp]

theorem e_child_curvature_mass_identity (u : ℝ) (hu0 : 0 < u) (hu1 : u < 1) :
    8*(1-u)*(childCurveB u-childCurveA u/8)/u^3-eChildCurvatureBound u =
      2*(1-u)*(u^2-10*u+13)*(childMassUpper u-phi u)/u^3 := by
  dsimp [childCurveA, childCurveB, childMassUpper, eChildCurvatureBound]
  have h1 := ne_of_gt (sub_pos.mpr hu1)
  have h2 : 2-u ≠ 0 := ne_of_gt (by linarith : 0 < 2-u)
  have h2' : u-2 ≠ 0 := by linarith
  field_simp [h1, h2, h2', ne_of_gt hu0]
  ring

theorem e_child_curvature_numerator (u T : ℝ) (hu0 : 0 < u) (huq : u ≤ (8/13 : ℝ))
    (hT : -(1/8 : ℝ) ≤ T) :
    (3/2 : ℝ)*(childCurveW u)^3 < (1-u)*(childCurveA u*T+childCurveB u) := by
  have hu1 : u < 1 := by linarith
  have h1 : 0 < 1-u := sub_pos.mpr hu1
  have hc : 0 ≤ u^2-10*u+13 := by nlinarith only [huq, sq_nonneg u]
  have hm := phi_rational_upper u hu0.le hu1
  have hrem : 0 ≤ 2*(1-u)*(u^2-10*u+13)*(childMassUpper u-phi u)/u^3 := by positivity
  have hid := e_child_curvature_mass_identity u hu0 hu1
  have hr := e_child_curvature_rational_lower u hu0 huq
  have hmass : (3/2 : ℝ) < 8*(1-u)*(childCurveB u-childCurveA u/8)/u^3 := by
    linarith only [hid, hrem, hr]
  have hmass' := (lt_div_iff₀ (pow_pos hu0 3)).mp hmass
  have hA := childCurveA_nonnegative u hu0.le hu1
  have hTmul := mul_nonneg hA (show 0 ≤ T+1/8 by linarith)
  have hTmul' := mul_nonneg h1.le hTmul
  have hw := child_w_bounds u hu0 hu1
  have hw3 : (childCurveW u)^3 ≤ (u/2)^3 := pow_le_pow_left₀ hw.1.le hw.2 3
  nlinarith only [hmass', hTmul', hw3]

theorem e_child_corrected_slope_derivative_positive (e u : ℝ) (he : 0 < e)
    (hu0 : 0 < u) (huq : u ≤ (8/13 : ℝ))
    (hT : -(1/8 : ℝ) ≤ childCurveT e u) :
    0 < deriv (fun x => childCurveV e x+(3/2 : ℝ)*childH x) u := by
  have hu1 : u < 1 := by linarith
  have hv := childCurveV_derivative e u he hu0 hu1
  have hh := (childH_derivative u hu0 hu1).const_mul (3/2)
  change 0 < deriv (childCurveV e + fun y => (3/2 : ℝ)*childH y) u
  rw [(hv.add hh).deriv]
  have hphi := phi_positive u hu0 hu1
  have hw : 0 < childCurveW u := (child_w_bounds u hu0 hu1).1
  have hnum := e_child_curvature_numerator u (childCurveT e u) hu0 huq hT
  have heq : (childCurveA u*childCurveT e u+childCurveB u)/(phi u*(childCurveW u)^2)+
      (3/2)*(-childCurveW u/((1-u)*phi u)) =
      ((1-u)*(childCurveA u*childCurveT e u+childCurveB u)-(3/2)*(childCurveW u)^3)/
      ((1-u)*phi u*(childCurveW u)^2) := by
    field_simp [ne_of_gt hphi, ne_of_gt hw, ne_of_gt (sub_pos.mpr hu1)]
    ring
  rw [heq]
  exact div_pos (sub_pos.mpr hnum) (by positivity)

end F4Heavy.Analysis
