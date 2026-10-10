module

public import F4Heavy.Analysis.DHDenominator10
public import F4Heavy.Analysis.DFCombine0

public import F4Heavy.Analysis.DIdentityCoordinates

public import F4Heavy.Analysis.ConnectionSquareForms

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem d_F0_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_endpoint_F0 v x = (18897856102400000000000000000000000000000000000000000000/9 : ℝ)*dFNum v x (dLowerNum v x) (1+x) := by
  rw [d_F0_pieces, d_F0_piece0_value, d_F0_piece1_value, d_F0_piece2_value, d_F0_piece3_value, d_F0_piece4_value, d_F0_piece5_value]
  rw [← realMatrixValue_coefficients, d_F0_coefficient_identity, realMatrixValue_scale, d_F0_combined_value]

def d_F0_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow reflectDBase 3)) reflectDVacancy) (.add (.const ⟨(1), 1⟩) .parent)) reflectDSupport)

def d_F0_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(22372200151188480), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 3)) (.add .activity (.const ⟨(1), 1⟩))) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3)) (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .activity 2) (.const ⟨(1), 20⟩)))) (.mul (.mul (.const ⟨(9), 1⟩) .activity) (.const ⟨(1), 10⟩))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(81), 20⟩)))) (.add .parent (.const ⟨(1), 1⟩)))

def d_F0_denominator_identity_scalar_left_expression : PolynomialExpr :=
  (.const ⟨(5254814924942274065823784413892713853747200000000000000000000000000000000000000000000000), 1⟩)

def d_F0_denominator_identity_scalar_right_expression : PolynomialExpr :=
  (.mul (.mul (.const ⟨(18897856102400000000000000000000000000000000000000000000), 9⟩) (.const ⟨(5), 1⟩)) (.pow (.const ⟨(22372200151188480), 1⟩) 2))

set_option maxRecDepth 4096 in
theorem d_F0_denominator_identity_coefficients_check : PolynomialExpr.check d_F0_denominator_identity_left_expression d_F0_denominator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem d_F0_denominator_identity_scalar_check : PolynomialExpr.check d_F0_denominator_identity_scalar_left_expression d_F0_denominator_identity_scalar_right_expression = true := by
  decide +kernel

theorem d_F0_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_F0_denominator v x = (18897856102400000000000000000000000000000000000000000000/9 : ℝ)*dFDen v x (1+x) := by
  have hi : 12*(1-v)^2*(dBase v x)^3*dVacancyDen v x*(1+x)*dSupportDen v = 22372200151188480*(v-1)^3*(v+1)*(v*x-v/4+x+9/4)^3*(v^2*x-v^2/20+9*v/10-x-81/20)*(x+1) := by
    have hp := PolynomialExpr.check_sound _ _ d_F0_denominator_identity_coefficients_check v x
    simpa only [d_F0_denominator_identity_left_expression, d_F0_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDVacancy_value, reflectDSupport_value, dFDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp
  have hs : (5254814924942274065823784413892713853747200000000000000000000000000000000000000000000000/1 : ℝ) = (18897856102400000000000000000000000000000000000000000000/9 : ℝ)*(5*(22372200151188480 : ℝ)^2) := by
    have hp := PolynomialExpr.check_sound _ _ d_F0_denominator_identity_scalar_check 0 0
    simpa only [d_F0_denominator_identity_scalar_left_expression,d_F0_denominator_identity_scalar_right_expression,d_F0_denominator_identity_left_expression, d_F0_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDVacancy_value, reflectDSupport_value, dFDen, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp
  rw [dh_record_D_r6_endpoint_F0_denominator_value]
  unfold dFDen
  rw [hi,hs]
  convert connection_square_product (18897856102400000000000000000000000000000000000000000000/9 : ℝ) 22372200151188480 (v-1) (v+1)
    (v*x-v/4+x+9/4) (v^2*x-v^2/20+9*v/10-x-81/20) (x+1) using 1 <;> ac_rfl

theorem dh_record_D_F0_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_endpoint_F0 v x = dFFormula (dActivity v) x (parentLogLower .D (dActivity v) x) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hH := ne_of_gt (d_support_den_positive v hv)
  have hT : (1+x) ≠ 0 := ne_of_gt (by linarith only [hx.1])
  rw [d_F_formula_coordinate v x _ (dLowerNum v x) (1+x) hq hB hS hT hH
    (d_lower_coordinate v x hq hT)]
  unfold dh_record_D_r6_endpoint_F0
  rw [d_F0_numerator_identity, d_F0_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (18897856102400000000000000000000000000000000000000000000/9 : ℝ) ≠ 0)

theorem d_F0_guard_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dFFormula lam x (parentLogLower .D lam x) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hf := dh_record_D_F0_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_D_r6_endpoint_F0_positive _ x hv hx

end F4Heavy.Analysis
