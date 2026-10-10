module

public import F4Heavy.Analysis.ChildCurve

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def childCurvatureRational (m u : ℝ) : ℝ :=
  8*(1-u)*(3*u-3*m*u^2+2*m*u-(3-2*u+2*m*(1-u)^2)*childMassUpper u)/u^3

theorem child_curvature_mass_identity (m u : ℝ) :
    8*(1-u)*(childCurveB u-m*childCurveA u)/u^3-childCurvatureRational m u =
      8*(1-u)*(3-2*u+2*m*(1-u)^2)*(childMassUpper u-phi u)/u^3 := by
  dsimp [childCurvatureRational, childCurveA, childCurveB]
  ring

theorem child_curvature_numerator (m k u T : ℝ) (hm0 : 0 ≤ m) (hk : 0 < k)
    (hu0 : 0 < u) (hu1 : u < 1) (hT : -m ≤ T)
    (hR : k < childCurvatureRational m u) :
    k*(childCurveW u)^3 < (1-u)*(childCurveA u*T+childCurveB u) := by
  have h1 : 0 < 1-u := sub_pos.mpr hu1
  have hc : 0 ≤ 3-2*u+2*m*(1-u)^2 := by
    have h2 : 0 ≤ 2*m*(1-u)^2 := by positivity
    linarith only [h2, hu1]
  have hm := phi_rational_upper u hu0.le hu1
  have hrem : 0 ≤ 8*(1-u)*(3-2*u+2*m*(1-u)^2)*(childMassUpper u-phi u)/u^3 := by positivity
  have hid := child_curvature_mass_identity m u
  have hmass : k < 8*(1-u)*(childCurveB u-m*childCurveA u)/u^3 := by
    linarith only [hid, hrem, hR]
  have hmass' := (lt_div_iff₀ (pow_pos hu0 3)).mp hmass
  have hA := childCurveA_nonnegative u hu0.le hu1
  have hTmul := mul_nonneg h1.le (mul_nonneg hA (show 0 ≤ T+m by linarith only [hT]))
  have hw := child_w_bounds u hu0 hu1
  have hw3 : (childCurveW u)^3 ≤ (u/2)^3 := pow_le_pow_left₀ hw.1.le hw.2 3
  have hw3k := mul_le_mul_of_nonneg_left hw3 hk.le
  nlinarith only [hmass', hTmul, hw3k]

theorem child_corrected_slope_derivative_positive (e k u : ℝ) (he : 0 < e)
    (hu0 : 0 < u) (hu1 : u < 1)
    (hnum : k*(childCurveW u)^3 < (1-u)*(childCurveA u*childCurveT e u+childCurveB u)) :
    0 < deriv (fun x => childCurveV e x+k*childH x) u := by
  have hv := childCurveV_derivative e u he hu0 hu1
  have hh := (childH_derivative u hu0 hu1).const_mul k
  change 0 < deriv (childCurveV e + fun y => k*childH y) u
  rw [(hv.add hh).deriv]
  have hphi := phi_positive u hu0 hu1
  have hw : 0 < childCurveW u := (child_w_bounds u hu0 hu1).1
  have heq : (childCurveA u*childCurveT e u+childCurveB u)/(phi u*(childCurveW u)^2)+
      k*(-childCurveW u/((1-u)*phi u)) =
      ((1-u)*(childCurveA u*childCurveT e u+childCurveB u)-k*(childCurveW u)^3)/
      ((1-u)*phi u*(childCurveW u)^2) := by
    field_simp [ne_of_gt hphi, ne_of_gt hw, ne_of_gt (sub_pos.mpr hu1)]
    ring
  rw [heq]
  exact div_pos (sub_pos.mpr hnum) (by positivity)

end F4Heavy.Analysis
