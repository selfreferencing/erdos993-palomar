module

public import F4Heavy.Analysis.DHDenominator34
public import F4Heavy.Analysis.HUpperWCombine1V0
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem hUW1V0_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_1_1_V0 v x*((hBase v x)^3) =
      (2999960301782171648000000000000000000000000000000000000000000/27 : ℝ)*hUpperWNum v x (hUpperNum v x) (eLogDen x) (hVertexNum v 0) (hHeightNum v 0) := by
  unfold hUpperWNum
  rw [hUW1V0_piece0_value, hUW1V0_piece1_value, hUW1V0_piece2_value, hUW1V0_piece3_value, hUW1V0_piece4_value]
  rw [hUW1V0_lift_value, ← realMatrixValue_coefficients, hUW1V0_coefficient_identity, realMatrixValue_scale, hUW1V0_combined_value]

def hUW1V0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(1986610524304217172926672208376094062577442619392000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.const ⟨(11), 3⟩)) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 2)) (.pow sampleBase 3))

def hUW1V0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(2999960301782171648000000000000000000000000000000000000000000), 27⟩) (.mul (.mul (.mul (.mul (.mul (.const ⟨(288), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) (.pow sampleBase 6)) (.pow batchLogDen 2)) (.pow sampleSupport 2)))

set_option maxRecDepth 4096 in
theorem hUW1V0_denominator_identity_coefficients_check : PolynomialExpr.check hUW1V0_denominator_identity_left_expression hUW1V0_denominator_identity_right_expression = true := by
  decide +kernel

theorem hUW1V0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_1_1_V0_denominator v x*((hBase v x)^3) = (2999960301782171648000000000000000000000000000000000000000000/27 : ℝ)*hUpperWDen v x (eLogDen x) := by
  rw [dh_record_H_r6_1_1_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ hUW1V0_denominator_identity_coefficients_check v x
  simpa only [hUW1V0_denominator_identity_left_expression, hUW1V0_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, batchLogDen_value, hUpperWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_hUW1V0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_1_1_V0 v x = dhWFormula .H (hActivity v) x 1 (parentLogUpper .H (hActivity v) x)
      (hUpperSupportVertex (hActivity v) 0) (hUpperSupportHeight (hActivity v) 0) := by
  obtain ⟨hq, hA, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hH := ne_of_gt (h_support_den_positive v hv)
  have hT : (eLogDen x) ≠ 0 := h_log_denominator_nonzero x hx.1
  have hU : v+1 ≠ 0 := ne_of_gt (by linarith only [hv.1])
  have hf : ((hBase v x)^3) ≠ 0 := by positivity
  rw [h_upper_W_coordinate v x _ (hUpperNum v x) (eLogDen x) 0 hq hA hB hT hH (h_upper_coordinate v x hq hT)]
  unfold dh_record_H_r6_1_1_V0
  calc
    _ = (matrixValue numerator_H_r6_1_1_V0 v x*((hBase v x)^3))/(polynomialValue dh_record_H_r6_1_1_V0_denominator v x*((hBase v x)^3)) :=
      (mul_div_mul_right _ _ hf).symm
    _ = _ := by
      rw [hUW1V0_numerator_identity, hUW1V0_denominator_identity]
      exact mul_div_mul_left _ _ (by norm_num : (2999960301782171648000000000000000000000000000000000000000000/27 : ℝ) ≠ 0)

theorem hUW1V0_primary_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x 1 (parentLogUpper .H lam x) (hUpperSupportVertex lam 0) (hUpperSupportHeight lam 0) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hh := dh_record_hUW1V0_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hh
  rw [he] at hh
  rw [← hh]
  exact dh_record_H_r6_1_1_V0_positive _ x hv hx

end F4Heavy.Analysis
