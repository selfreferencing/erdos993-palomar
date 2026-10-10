module

public import F4Heavy.Analysis.DHDenominator01
public import F4Heavy.Analysis.DUpperWCombine0V0

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem dUW0V0_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_1_0_V0 v x*((dBase v x)^3) =
      (831505668505600000000000000000000000000000000000000000/27 : ℝ)*dUpperWNum v x (dLowerNum v x) (1+x) (dVertexNum v 0) (dHeightNum v 0) := by
  unfold dUpperWNum
  rw [dUW0V0_piece0_value, dUW0V0_piece1_value, dUW0V0_piece2_value, dUW0V0_piece3_value, dUW0V0_piece4_value]
  rw [dUW0V0_lift_value, ← realMatrixValue_coefficients, dUW0V0_coefficient_identity, realMatrixValue_scale, dUW0V0_combined_value]

def dUW0V0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(-60211421014963557004230863075854012907520000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(9), 1⟩))) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3)) (.pow reflectDBase 3))

def dUW0V0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(831505668505600000000000000000000000000000000000000000), 27⟩) (.mul (.mul (.mul (.mul (.mul (.const ⟨(14400), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 6)) (.pow (.add (.const ⟨(1), 1⟩) .parent) 2)) (.pow reflectDSupport 2)))

set_option maxRecDepth 4096 in
theorem dUW0V0_denominator_identity_coefficients_check : PolynomialExpr.check dUW0V0_denominator_identity_left_expression dUW0V0_denominator_identity_right_expression = true := by
  decide +kernel

theorem dUW0V0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_1_0_V0_denominator v x*((dBase v x)^3) = (831505668505600000000000000000000000000000000000000000/27 : ℝ)*dUpperWDen v x (1+x) := by
  rw [dh_record_D_r6_1_0_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ dUW0V0_denominator_identity_coefficients_check v x
  simpa only [dUW0V0_denominator_identity_left_expression, dUW0V0_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDSupport_value, dUpperWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_dUW0V0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_1_0_V0 v x = dhWFormula .D (dActivity v) x 1 (parentLogLower .D (dActivity v) x)
      (dSupportVertex (dActivity v) 0) (dSupportHeight (dActivity v) 0) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hA : 9-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hH := ne_of_gt (d_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  have hU : v+1 ≠ 0 := ne_of_gt (by linarith only [hv.1])
  have hf : ((dBase v x)^3) ≠ 0 := by positivity
  rw [d_upper_W_coordinate v x _ (dLowerNum v x) (1+x) 0 hq hA hB hT hH (d_lower_coordinate v x hq hT)]
  unfold dh_record_D_r6_1_0_V0
  calc
    _ = (matrixValue numerator_D_r6_1_0_V0 v x*((dBase v x)^3))/(polynomialValue dh_record_D_r6_1_0_V0_denominator v x*((dBase v x)^3)) :=
      (mul_div_mul_right _ _ hf).symm
    _ = _ := by
      rw [dUW0V0_numerator_identity, dUW0V0_denominator_identity]
      exact mul_div_mul_left _ _ (by norm_num : (831505668505600000000000000000000000000000000000000000/27 : ℝ) ≠ 0)

theorem dUW0V0_primary_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x 1 (parentLogLower .D lam x) (dSupportVertex lam 0) (dSupportHeight lam 0) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hh := dh_record_dUW0V0_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hh
  rw [he] at hh
  rw [← hh]
  exact dh_record_D_r6_1_0_V0_positive _ x hv hx

end F4Heavy.Analysis
