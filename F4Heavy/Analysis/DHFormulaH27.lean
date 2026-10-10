module

public import F4Heavy.Analysis.DHDenominator27
public import F4Heavy.Analysis.HLowerWCombine0
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem h_LW0_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_0_0_V0 v x = (562949953421312000000000000000000000000000000000000000000/1 : ℝ)*hLowerWNum v x (hLowerNum v x) (1+x) := by
  unfold hLowerWNum
  rw [h_LW0_piece0_value, h_LW0_piece1_value, h_LW0_piece2_value, h_LW0_piece3_value]
  rw [← realMatrixValue_coefficients, h_LW0_coefficient_identity, realMatrixValue_scale, h_LW0_combined_value]

def h_LW0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(-289949618859688501292439804395918734764539904000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.const ⟨(11), 3⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(9), 1⟩) (.pow .activity 2)) (.const ⟨(1), 28⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(33), 1⟩) .activity) (.const ⟨(1), 14⟩)))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(121), 28⟩))) 1))

def h_LW0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(562949953421312000000000000000000000000000000000000000000), 1⟩) (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(24), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) (.pow sampleBase 3)) batchVacancy) (.pow (.add (.const ⟨(1), 1⟩) .parent) 2)) (.pow sampleSupport 2)))

set_option maxRecDepth 4096 in
theorem h_LW0_denominator_identity_coefficients_check : PolynomialExpr.check h_LW0_denominator_identity_left_expression h_LW0_denominator_identity_right_expression = true := by
  decide +kernel

theorem h_LW0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_0_0_V0_denominator v x = (562949953421312000000000000000000000000000000000000000000/1 : ℝ)*hLowerWDen v x (1+x) := by
  rw [dh_record_H_r6_0_0_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ h_LW0_denominator_identity_coefficients_check v x
  simpa only [h_LW0_denominator_identity_left_expression, h_LW0_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, batchVacancy_value, hLowerWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_H_LW0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_0_0_V0 v x = dhWFormula .H (hActivity v) x (dhVacancyX (hActivity v) x)
      (parentLogLower .H (hActivity v) x) (hSupportVertex (hActivity v) 0) 0 := by
  obtain ⟨hq, hA, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hH := ne_of_gt (h_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  rw [h_lower_W_coordinate v x _ (hLowerNum v x) (1+x) hq hA hB hS hT hH (h_lower_coordinate v x hq hT)]
  unfold dh_record_H_r6_0_0_V0
  rw [h_LW0_numerator_identity, h_LW0_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (562949953421312000000000000000000000000000000000000000000/1 : ℝ) ≠ 0)

theorem h_LW0_primary_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x (dhVacancyX lam x) (parentLogLower .H lam x) (hSupportVertex lam 0) 0 := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_LW0_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_0_0_V0_positive _ x hv hx

end F4Heavy.Analysis
