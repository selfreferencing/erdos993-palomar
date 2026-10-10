module

public import F4Heavy.Analysis.DHDenominator33
public import F4Heavy.Analysis.HLowerWCombine1
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem h_LW1_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_0_1_V0 v x = (11999841207128686592000000000000000000000000000000000000000000/9 : ℝ)*hLowerWNum v x (hUpperNum v x) (eLogDen x) := by
  unfold hLowerWNum
  rw [h_LW1_piece0_value, h_LW1_piece1_value, h_LW1_piece2_value, h_LW1_piece3_value]
  rw [← realMatrixValue_coefficients, h_LW1_coefficient_identity, realMatrixValue_scale, h_LW1_combined_value]

def h_LW1_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(-55625094680518080841946821834530633752168393342976000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.const ⟨(11), 3⟩)) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(9), 1⟩) (.pow .activity 2)) (.const ⟨(1), 28⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(33), 1⟩) .activity) (.const ⟨(1), 14⟩)))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(121), 28⟩))) 1)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 2))

def h_LW1_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(11999841207128686592000000000000000000000000000000000000000000), 9⟩) (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(24), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) (.pow sampleBase 3)) batchVacancy) (.pow batchLogDen 2)) (.pow sampleSupport 2)))

set_option maxRecDepth 4096 in
theorem h_LW1_denominator_identity_coefficients_check : PolynomialExpr.check h_LW1_denominator_identity_left_expression h_LW1_denominator_identity_right_expression = true := by
  decide +kernel

theorem h_LW1_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_0_1_V0_denominator v x = (11999841207128686592000000000000000000000000000000000000000000/9 : ℝ)*hLowerWDen v x (eLogDen x) := by
  rw [dh_record_H_r6_0_1_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ h_LW1_denominator_identity_coefficients_check v x
  simpa only [h_LW1_denominator_identity_left_expression, h_LW1_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, batchVacancy_value, batchLogDen_value, hLowerWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_H_LW1_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_0_1_V0 v x = dhWFormula .H (hActivity v) x (dhVacancyX (hActivity v) x)
      (parentLogUpper .H (hActivity v) x) (hSupportVertex (hActivity v) 0) 0 := by
  obtain ⟨hq, hA, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hH := ne_of_gt (h_support_den_positive v hv)
  have hT : (eLogDen x) ≠ 0 := h_log_denominator_nonzero x hx.1
  rw [h_lower_W_coordinate v x _ (hUpperNum v x) (eLogDen x) hq hA hB hS hT hH (h_upper_coordinate v x hq hT)]
  unfold dh_record_H_r6_0_1_V0
  rw [h_LW1_numerator_identity, h_LW1_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (11999841207128686592000000000000000000000000000000000000000000/9 : ℝ) ≠ 0)

theorem h_LW1_primary_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x (dhVacancyX lam x) (parentLogUpper .H lam x) (hSupportVertex lam 0) 0 := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_LW1_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_0_1_V0_positive _ x hv hx

end F4Heavy.Analysis
