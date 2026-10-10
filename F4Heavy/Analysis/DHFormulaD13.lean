module

public import F4Heavy.Analysis.DHDenominator13
public import F4Heavy.Analysis.DLowerCoordinates

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dCNum (v x : ℝ) : ℝ :=
  240*dDeltaNum v*(dBase v x)^3*dVacancyDen v x-
    11*dProbNum v x*(2*dParentLowerNum v x-(dAlphaNum v+dBetaNum v)*12*(dBase v x)^2*dVacancyDen v x)

def d_C_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_D_r6_endpoint_C)

def d_C_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(5242880), 1⟩) (.add (.mul (.mul (.mul (.const ⟨(240), 1⟩) reflectDDelta) (.pow reflectDBase 3)) reflectDVacancy) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(11), 1⟩) reflectDProb) (.add (.mul (.const ⟨(2), 1⟩) reflectDParentLower) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.add reflectDAlpha reflectDBeta) (.const ⟨(12), 1⟩)) (.pow reflectDBase 2)) reflectDVacancy)))))))

set_option maxRecDepth 4096 in
theorem d_C_numerator_identity_coefficients_check : PolynomialExpr.check d_C_numerator_identity_left_expression d_C_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem d_C_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_endpoint_C v x = 5242880*dCNum v x := by
  have h := PolynomialExpr.check_sound _ _ d_C_numerator_identity_coefficients_check v x
  simpa only [d_C_numerator_identity_left_expression, d_C_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectDAlpha_value, reflectDBase_value, reflectDBeta_value, reflectDDelta_value, reflectDParentLower_value, reflectDProb_value, reflectDVacancy_value, dCNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def d_C_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.const ⟨(402653184000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .activity 2) (.const ⟨(1), 20⟩)))) (.mul (.mul (.const ⟨(9), 1⟩) .activity) (.const ⟨(1), 10⟩))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(81), 20⟩))) 1))

def d_C_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(5242880), 1⟩) (.mul (.mul (.mul (.const ⟨(60), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 3)) reflectDVacancy))

set_option maxRecDepth 4096 in
theorem d_C_denominator_identity_coefficients_check : PolynomialExpr.check d_C_denominator_identity_left_expression d_C_denominator_identity_right_expression = true := by
  decide +kernel

theorem d_C_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_C_denominator v x =
      5242880*(60*(1-v)*(dBase v x)^3*dVacancyDen v x) := by
  rw [dh_record_D_r6_endpoint_C_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ d_C_denominator_identity_coefficients_check v x
  simpa only [d_C_denominator_identity_left_expression, d_C_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDVacancy_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_D_C_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_endpoint_C v x =
      4*delta .D (dActivity v)-(11/5)*(eProbabilityX (dActivity v) x *
        (2*dhParentUpperX .D (dActivity v) x (dhVacancyX (dActivity v) x)-
          alpha .D (dActivity v)-beta .D (dActivity v))) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  rw [d_probability_coordinate v x hq hB, d_alpha_coordinate v hq,
    d_beta_coordinate v hq, d_delta_coordinate v hq, d_parent_lower_coordinate v x hq hB hS]
  rw [dh_C_clear _ _ _ _ _ _ _ _ hq hB hS]
  change dh_record_D_r6_endpoint_C v x = dCNum v x/(60*(1-v)*(dBase v x)^3*dVacancyDen v x)
  unfold dh_record_D_r6_endpoint_C
  rw [d_C_numerator_identity, d_C_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (5242880 : ℝ) ≠ 0)

theorem d_C_guard_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < 4*delta .D lam-(11/5)*(eProbabilityX lam x *
      (2*dhParentUpperX .D lam x (dhVacancyX lam x)-alpha .D lam-beta .D lam)) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hf := dh_record_D_C_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_D_r6_endpoint_C_positive _ x hv hx

end F4Heavy.Analysis
