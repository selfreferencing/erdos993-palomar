module

public import F4Heavy.Analysis.DHDenominator04
public import F4Heavy.Analysis.DUpperWCombine0V3

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem dUW0V3_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_1_0_V3 v x*((1-v)*(v+1)^2*dBase v x) =
      (536870912000000000000000000000000000000000000/4369570342029 : ℝ)*dUpperWNum v x (dLowerNum v x) (1+x) (dVertexNum v 3) (dHeightNum v 3) := by
  unfold dUpperWNum
  rw [dUW0V3_piece0_value, dUW0V3_piece1_value, dUW0V3_piece2_value, dUW0V3_piece3_value, dUW0V3_piece4_value]
  rw [dUW0V3_lift_value, ← realMatrixValue_coefficients, dUW0V3_coefficient_identity, realMatrixValue_scale, dUW0V3_combined_value]

def dUW0V3_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(3843514719556831085278003200000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 5)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(9), 1⟩))) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 5)) (.mul (.mul (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) reflectDBase))

def dUW0V3_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(536870912000000000000000000000000000000000000), 4369570342029⟩) (.mul (.mul (.mul (.mul (.mul (.const ⟨(14400), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 6)) (.pow (.add (.const ⟨(1), 1⟩) .parent) 2)) (.pow reflectDSupport 2)))

set_option maxRecDepth 4096 in
theorem dUW0V3_denominator_identity_coefficients_check : PolynomialExpr.check dUW0V3_denominator_identity_left_expression dUW0V3_denominator_identity_right_expression = true := by
  decide +kernel

theorem dUW0V3_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_1_0_V3_denominator v x*((1-v)*(v+1)^2*dBase v x) = (536870912000000000000000000000000000000000000/4369570342029 : ℝ)*dUpperWDen v x (1+x) := by
  rw [dh_record_D_r6_1_0_V3_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ dUW0V3_denominator_identity_coefficients_check v x
  simpa only [dUW0V3_denominator_identity_left_expression, dUW0V3_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDSupport_value, dUpperWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_dUW0V3_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_1_0_V3 v x = dhWFormula .D (dActivity v) x 1 (parentLogLower .D (dActivity v) x)
      (dSupportVertex (dActivity v) 3) (dSupportHeight (dActivity v) 3) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hA : 9-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hH := ne_of_gt (d_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  have hU : v+1 ≠ 0 := ne_of_gt (by linarith only [hv.1])
  have hf : ((1-v)*(v+1)^2*dBase v x) ≠ 0 := by positivity
  rw [d_upper_W_coordinate v x _ (dLowerNum v x) (1+x) 3 hq hA hB hT hH (d_lower_coordinate v x hq hT)]
  unfold dh_record_D_r6_1_0_V3
  calc
    _ = (matrixValue numerator_D_r6_1_0_V3 v x*((1-v)*(v+1)^2*dBase v x))/(polynomialValue dh_record_D_r6_1_0_V3_denominator v x*((1-v)*(v+1)^2*dBase v x)) :=
      (mul_div_mul_right _ _ hf).symm
    _ = _ := by
      rw [dUW0V3_numerator_identity, dUW0V3_denominator_identity]
      exact mul_div_mul_left _ _ (by norm_num : (536870912000000000000000000000000000000000000/4369570342029 : ℝ) ≠ 0)

theorem dUW0V3_primary_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x 1 (parentLogLower .D lam x) (dSupportVertex lam 3) (dSupportHeight lam 3) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hh := dh_record_dUW0V3_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hh
  rw [he] at hh
  rw [← hh]
  exact dh_record_D_r6_1_0_V3_positive _ x hv hx

end F4Heavy.Analysis
