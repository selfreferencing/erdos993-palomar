module

public import F4Heavy.Analysis.DHDenominator39
public import F4Heavy.Analysis.HGuardCore
public import F4Heavy.Analysis.HFCombine0

public import F4Heavy.Analysis.HIdentityCoordinates

public import F4Heavy.Analysis.ConnectionSquareForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem h_F0_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_endpoint_F0 v x = (281474976710656000000000000000000000000000000000000000000/3 : ℝ)*hFNum v x (hLowerNum v x) (1+x) := by
  rw [h_F0_pieces, h_F0_piece0_value, h_F0_piece1_value, h_F0_piece2_value, h_F0_piece3_value, h_F0_piece4_value, h_F0_piece5_value]
  rw [← realMatrixValue_coefficients, h_F0_coefficient_identity, realMatrixValue_scale, h_F0_combined_value]

def h_F0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow sampleBase 3)) batchVacancy) (.add (.const ⟨(1), 1⟩) .parent)) sampleSupport)

def h_F0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(99464350457498544), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 3)) (.add .activity (.const ⟨(1), 1⟩))) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(9), 1⟩) (.pow .activity 2)) (.const ⟨(1), 28⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(33), 1⟩) .activity) (.const ⟨(1), 14⟩)))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(121), 28⟩)))) (.add .parent (.const ⟨(1), 1⟩)))

def h_F0_denominator_identity_scalar_left_expression : PolynomialExpr :=
  (.const ⟨(4641126899214080610687653135697339214464402063360000000000000000000000000000000000000000000), 1⟩)

def h_F0_denominator_identity_scalar_right_expression : PolynomialExpr :=
  (.mul (.mul (.const ⟨(281474976710656000000000000000000000000000000000000000000), 3⟩) (.const ⟨(5), 1⟩)) (.pow (.const ⟨(99464350457498544), 1⟩) 2))

set_option maxRecDepth 4096 in
theorem h_F0_denominator_identity_coefficients_check : PolynomialExpr.check h_F0_denominator_identity_left_expression h_F0_denominator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem h_F0_denominator_identity_scalar_check : PolynomialExpr.check h_F0_denominator_identity_scalar_left_expression h_F0_denominator_identity_scalar_right_expression = true := by
  decide +kernel

theorem h_F0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_F0_denominator v x = (281474976710656000000000000000000000000000000000000000000/3 : ℝ)*hFDen v x (1+x) := by
  have hi : 12*(1-v)^2*(hBase v x)^3*hVacancyDen v x*(1+x)*hSupportDen v = 99464350457498544*(v-1)^3*(v+1)*(v*x+3*v/7+x+11/7)^3*(v^2*x-9*v^2/28-33*v/14-x-121/28)*(x+1) := by
    have hp := PolynomialExpr.check_sound _ _ h_F0_denominator_identity_coefficients_check v x
    simpa only [h_F0_denominator_identity_left_expression, h_F0_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, batchVacancy_value, hFDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp
  have hs : (4641126899214080610687653135697339214464402063360000000000000000000000000000000000000000000/1 : ℝ) = (281474976710656000000000000000000000000000000000000000000/3 : ℝ)*(5*(99464350457498544 : ℝ)^2) := by
    have hp := PolynomialExpr.check_sound _ _ h_F0_denominator_identity_scalar_check 0 0
    simpa only [h_F0_denominator_identity_scalar_left_expression,h_F0_denominator_identity_scalar_right_expression,h_F0_denominator_identity_left_expression, h_F0_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, sampleSupport_value, batchVacancy_value, hFDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp
  rw [dh_record_H_r6_endpoint_F0_denominator_value]
  unfold hFDen
  rw [hi,hs]
  convert connection_square_product (281474976710656000000000000000000000000000000000000000000/3 : ℝ) 99464350457498544 (v-1) (v+1)
    (v*x+3*v/7+x+11/7) (v^2*x-9*v^2/28-33*v/14-x-121/28) (x+1) using 1 <;> ac_rfl

theorem dh_record_H_F0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_endpoint_F0 v x = hFFormula (hActivity v) x (parentLogLower .H (hActivity v) x) := by
  obtain ⟨hq, _, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hH := ne_of_gt (h_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  rw [h_F_formula_coordinate v x _ (hLowerNum v x) (1+x) hq hB hS hT hH
    (h_lower_coordinate v x hq hT)]
  unfold dh_record_H_r6_endpoint_F0
  rw [h_F0_numerator_identity, h_F0_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (281474976710656000000000000000000000000000000000000000000/3 : ℝ) ≠ 0)

theorem h_F0_guard_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < hFFormula lam x (parentLogLower .H lam x) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_F0_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_endpoint_F0_positive _ x hv hx

end F4Heavy.Analysis
