module

public import F4Heavy.Analysis.DHDenominator12
public import F4Heavy.Analysis.DUpperLogCoordinate

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dRNum (v x : ℝ) : ℝ :=
  dProbNum v x*(2*dParentLowerNum v x-(dAlphaNum v+dBetaNum v)*12*(dBase v x)^2*dVacancyDen v x)*
    (1-v)*eLogDen x+24*(dGammaNum v-dDeltaNum v)*(1-v)*(dBase v x)^3*dVacancyDen v x*eLogDen x-
    2*dProbNum v x*dUpperNum v x*dParentLowerNum v x

def d_R_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_D_r6_endpoint_R)

def d_R_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(3922984960000000000000), 1⟩) (.add (.add (.mul (.mul (.mul reflectDProb (.add (.mul (.const ⟨(2), 1⟩) reflectDParentLower) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.add reflectDAlpha reflectDBeta) (.const ⟨(12), 1⟩)) (.pow reflectDBase 2)) reflectDVacancy)))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDLogDen) (.mul (.mul (.mul (.mul (.mul (.const ⟨(24), 1⟩) (.add reflectDGamma (.mul (.const ⟨(-1), 1⟩) reflectDDelta))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 3)) reflectDVacancy) reflectDLogDen)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(2), 1⟩) reflectDProb) reflectDUpper) reflectDParentLower))))

set_option maxRecDepth 4096 in
theorem d_R_numerator_identity_coefficients_check : PolynomialExpr.check d_R_numerator_identity_left_expression d_R_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem d_R_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_endpoint_R v x = 3922984960000000000000*dRNum v x := by
  have h := PolynomialExpr.check_sound _ _ d_R_numerator_identity_coefficients_check v x
  simpa only [d_R_numerator_identity_left_expression, d_R_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectDAlpha_value, reflectDBase_value, reflectDBeta_value, reflectDDelta_value, reflectDGamma_value, reflectDLogDen_value, reflectDParentLower_value, reflectDProb_value, reflectDUpper_value, reflectDVacancy_value, dRNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def d_R_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(-542313440870400000000000000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.pow .activity 2) (.const ⟨(1), 20⟩)))) (.mul (.mul (.const ⟨(9), 1⟩) .activity) (.const ⟨(1), 10⟩))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(81), 20⟩))) 1)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1))

def d_R_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(3922984960000000000000), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow reflectDBase 3)) reflectDVacancy) reflectDLogDen))

set_option maxRecDepth 4096 in
theorem d_R_denominator_identity_coefficients_check : PolynomialExpr.check d_R_denominator_identity_left_expression d_R_denominator_identity_right_expression = true := by
  decide +kernel

theorem d_R_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_R_denominator v x =
      3922984960000000000000*(12*(1-v)^2*(dBase v x)^3*dVacancyDen v x*eLogDen x) := by
  rw [dh_record_D_r6_endpoint_R_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ d_R_denominator_identity_coefficients_check v x
  simpa only [d_R_denominator_identity_left_expression, d_R_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, reflectDVacancy_value, reflectDLogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_D_R_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_endpoint_R v x =
      eProbabilityX (dActivity v) x *
        (2*dhParentUpperX .D (dActivity v) x (dhVacancyX (dActivity v) x)-
          alpha .D (dActivity v)-beta .D (dActivity v))+
      2*(gamma .D (dActivity v)-delta .D (dActivity v)-
        eProbabilityX (dActivity v) x*parentLogUpper .D (dActivity v) x*
          dhParentUpperX .D (dActivity v) x (dhVacancyX (dActivity v) x)) := by
  obtain ⟨hq, hB, hS⟩ := d_coordinate_denominators v x hv hx
  have hT := d_log_denominator_nonzero x hx.1
  rw [d_probability_coordinate v x hq hB, d_alpha_coordinate v hq,
    d_beta_coordinate v hq, d_delta_coordinate v hq, d_gamma_coordinate v hq,
    d_parent_lower_coordinate v x hq hB hS, d_upper_coordinate v x hq hT]
  rw [dh_R_clear _ _ _ _ _ _ _ _ _ _ _ hq hB hS hT]
  change dh_record_D_r6_endpoint_R v x = dRNum v x/(12*(1-v)^2*(dBase v x)^3*dVacancyDen v x*eLogDen x)
  unfold dh_record_D_r6_endpoint_R
  rw [d_R_numerator_identity, d_R_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (3922984960000000000000 : ℝ) ≠ 0)

theorem d_R_guard_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < eProbabilityX lam x *
      (2*dhParentUpperX .D lam x (dhVacancyX lam x)-alpha .D lam-beta .D lam)+
      2*(gamma .D lam-delta .D lam-eProbabilityX lam x*parentLogUpper .D lam x*
        dhParentUpperX .D lam x (dhVacancyX lam x)) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hf := dh_record_D_R_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_D_r6_endpoint_R_positive _ x hv hx

end F4Heavy.Analysis
