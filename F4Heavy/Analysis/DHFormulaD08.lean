module

public import F4Heavy.Analysis.DHDenominator08
public import F4Heavy.Analysis.DUpperWCombine1V2

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem dUW1V2_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_1_1_V2 v x*(dBase v x) =
      (1298515302820085760000000000000000000000000000000000000000000/1 : ℝ)*dUpperWNum v x (dUpperNum v x) (eLogDen x) (dVertexNum v 2) (dHeightNum v 2) := by
  unfold dUpperWNum
  rw [dUW1V2_piece0_value, dUW1V2_piece1_value, dUW1V2_piece2_value, dUW1V2_piece3_value, dUW1V2_piece4_value]
  rw [dUW1V2_lift_value, ← realMatrixValue_coefficients, dUW1V2_coefficient_identity, realMatrixValue_scale, dUW1V2_combined_value]

def dUW1V2_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(-3290254565601187533594985012051674655074249867264000000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(9), 1⟩))) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 5)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 2)) reflectDBase)

def dUW1V2_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(1298515302820085760000000000000000000000000000000000000000000), 1⟩) (.mul (.mul (.mul (.mul (.mul (.const ⟨(14400), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 6)) (.pow reflectDLogDen 2)) (.pow reflectDSupport 2)))

set_option maxRecDepth 4096 in
theorem dUW1V2_denominator_identity_coefficients_check : PolynomialExpr.check dUW1V2_denominator_identity_left_expression dUW1V2_denominator_identity_right_expression = true := by
  decide +kernel

theorem dUW1V2_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_1_1_V2_denominator v x*(dBase v x) = (1298515302820085760000000000000000000000000000000000000000000/1 : ℝ)*dUpperWDen v x (eLogDen x) := by
  rw [dh_record_D_r6_1_1_V2_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ dUW1V2_denominator_identity_coefficients_check v x
  simpa only [dUW1V2_denominator_identity_left_expression, dUW1V2_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDLogDen_value, reflectDSupport_value, dUpperWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_dUW1V2_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_1_1_V2 v x = dhWFormula .D (dActivity v) x 1 (parentLogUpper .D (dActivity v) x)
      (dSupportVertex (dActivity v) 2) (dSupportHeight (dActivity v) 2) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hA : 9-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hH := ne_of_gt (d_support_den_positive v hv)
  have hT : (eLogDen x) ≠ 0 := d_log_denominator_nonzero x hx.1
  have hU : v+1 ≠ 0 := ne_of_gt (by linarith only [hv.1])
  have hf : (dBase v x) ≠ 0 := by positivity
  rw [d_upper_W_coordinate v x _ (dUpperNum v x) (eLogDen x) 2 hq hA hB hT hH (d_upper_coordinate v x hq hT)]
  unfold dh_record_D_r6_1_1_V2
  calc
    _ = (matrixValue numerator_D_r6_1_1_V2 v x*(dBase v x))/(polynomialValue dh_record_D_r6_1_1_V2_denominator v x*(dBase v x)) :=
      (mul_div_mul_right _ _ hf).symm
    _ = _ := by
      rw [dUW1V2_numerator_identity, dUW1V2_denominator_identity]
      exact mul_div_mul_left _ _ (by norm_num : (1298515302820085760000000000000000000000000000000000000000000/1 : ℝ) ≠ 0)

theorem dUW1V2_primary_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x 1 (parentLogUpper .D lam x) (dSupportVertex lam 2) (dSupportHeight lam 2) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hh := dh_record_dUW1V2_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hh
  rw [he] at hh
  rw [← hh]
  exact dh_record_D_r6_1_1_V2_positive _ x hv hx

end F4Heavy.Analysis
