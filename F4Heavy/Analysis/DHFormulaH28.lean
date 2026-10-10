module

public import F4Heavy.Analysis.DHDenominator28
public import F4Heavy.Analysis.HUpperWCombine0V0
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem hUW0V0_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_1_0_V0 v x*((hBase v x)^3) =
      (140737488355328000000000000000000000000000000000000000000/3 : ℝ)*hUpperWNum v x (hLowerNum v x) (1+x) (hVertexNum v 0) (hHeightNum v 0) := by
  unfold hUpperWNum
  rw [hUW0V0_piece0_value, hUW0V0_piece1_value, hUW0V0_piece2_value, hUW0V0_piece3_value, hUW0V0_piece4_value]
  rw [hUW0V0_lift_value, ← realMatrixValue_coefficients, hUW0V0_coefficient_identity, realMatrixValue_scale, hUW0V0_combined_value]

def hUW0V0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(10355343530703160760444278728425669098733568000000000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 2)) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 6)) (.pow (.add .activity (.const ⟨(11), 3⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow sampleBase 3))

def hUW0V0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(140737488355328000000000000000000000000000000000000000000), 3⟩) (.mul (.mul (.mul (.mul (.mul (.const ⟨(288), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 4)) (.add (.const ⟨(11), 1⟩) (.mul (.const ⟨(3), 1⟩) .activity))) (.pow sampleBase 6)) (.pow (.add (.const ⟨(1), 1⟩) .parent) 2)) (.pow sampleSupport 2)))

set_option maxRecDepth 4096 in
theorem hUW0V0_denominator_identity_coefficients_check : PolynomialExpr.check hUW0V0_denominator_identity_left_expression hUW0V0_denominator_identity_right_expression = true := by
  decide +kernel

theorem hUW0V0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_1_0_V0_denominator v x*((hBase v x)^3) = (140737488355328000000000000000000000000000000000000000000/3 : ℝ)*hUpperWDen v x (1+x) := by
  rw [dh_record_H_r6_1_0_V0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ hUW0V0_denominator_identity_coefficients_check v x
  simpa only [hUW0V0_denominator_identity_left_expression, hUW0V0_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, hUpperWDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_hUW0V0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_1_0_V0 v x = dhWFormula .H (hActivity v) x 1 (parentLogLower .H (hActivity v) x)
      (hUpperSupportVertex (hActivity v) 0) (hUpperSupportHeight (hActivity v) 0) := by
  obtain ⟨hq, hA, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hH := ne_of_gt (h_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  have hU : v+1 ≠ 0 := ne_of_gt (by linarith only [hv.1])
  have hf : ((hBase v x)^3) ≠ 0 := by positivity
  rw [h_upper_W_coordinate v x _ (hLowerNum v x) (1+x) 0 hq hA hB hT hH (h_lower_coordinate v x hq hT)]
  unfold dh_record_H_r6_1_0_V0
  calc
    _ = (matrixValue numerator_H_r6_1_0_V0 v x*((hBase v x)^3))/(polynomialValue dh_record_H_r6_1_0_V0_denominator v x*((hBase v x)^3)) :=
      (mul_div_mul_right _ _ hf).symm
    _ = _ := by
      rw [hUW0V0_numerator_identity, hUW0V0_denominator_identity]
      exact mul_div_mul_left _ _ (by norm_num : (140737488355328000000000000000000000000000000000000000000/3 : ℝ) ≠ 0)

theorem hUW0V0_primary_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x 1 (parentLogLower .H lam x) (hUpperSupportVertex lam 0) (hUpperSupportHeight lam 0) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hh := dh_record_hUW0V0_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hh
  rw [he] at hh
  rw [← hh]
  exact dh_record_H_r6_1_0_V0_positive _ x hv hx

end F4Heavy.Analysis
