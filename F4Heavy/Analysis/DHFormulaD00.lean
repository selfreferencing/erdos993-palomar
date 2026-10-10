module

public import F4Heavy.Analysis.DHDenominator00
public import F4Heavy.Analysis.DLowerWCombine0

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem d_LW0_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_0_0_V0 v x = (3326022674022400000000000000000000000000000000000000000/9 : ℝ)*dLowerWNum v x (dLowerNum v x) (1+x) := by
  unfold dLowerWNum
  rw [d_LW0_piece0_value, d_LW0_piece1_value, d_LW0_piece2_value, d_LW0_piece3_value]
  rw [← realMatrixValue_coefficients, d_LW0_coefficient_identity, realMatrixValue_scale, d_LW0_combined_value]

def d_LW0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(1204228420299271140084617261517080258150400000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(9), 1⟩))) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .activity 2) (.const ⟨(1), 20⟩)))) (.mul (.mul (.const ⟨(9), 1⟩) .activity) (.const ⟨(1), 10⟩))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(81), 20⟩))) 1))

def d_LW0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(3326022674022400000000000000000000000000000000000000000), 9⟩) (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(1200), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 3)) reflectDVacancy) (.pow (.add (.const ⟨(1), 1⟩) .parent) 2)) (.pow reflectDSupport 2)))

set_option maxRecDepth 4096 in
theorem d_LW0_denominator_identity_coefficients_check : PolynomialExpr.check d_LW0_denominator_identity_left_expression d_LW0_denominator_identity_right_expression = true := by
  decide +kernel

theorem d_LW0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_0_0_V0_denominator v x = (3326022674022400000000000000000000000000000000000000000/9 : ℝ)*dLowerWDen v x (1+x) := by
  rw [dh_record_D_r6_0_0_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ d_LW0_denominator_identity_coefficients_check v x
  simpa only [d_LW0_denominator_identity_left_expression, d_LW0_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDVacancy_value, reflectDSupport_value, dLowerWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_D_LW0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_0_0_V0 v x = dhWFormula .D (dActivity v) x (dhVacancyX (dActivity v) x)
      (parentLogLower .D (dActivity v) x) (dSupportVertex (dActivity v) 0) 0 := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hA : 9-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hH := ne_of_gt (d_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  rw [d_lower_W_coordinate v x _ (dLowerNum v x) (1+x) hq hA hB hS hT hH (d_lower_coordinate v x hq hT)]
  unfold dh_record_D_r6_0_0_V0
  rw [d_LW0_numerator_identity, d_LW0_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (3326022674022400000000000000000000000000000000000000000/9 : ℝ) ≠ 0)

theorem d_LW0_primary_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x (dhVacancyX lam x) (parentLogLower .D lam x) (dSupportVertex lam 0) 0 := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hf := dh_record_D_LW0_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_D_r6_0_0_V0_positive _ x hv hx

end F4Heavy.Analysis
