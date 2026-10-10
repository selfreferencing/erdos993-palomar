module

public import F4Heavy.Analysis.DHDenominator41
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hRNum (v x : ℝ) : ℝ :=
  hProbNum v x*(2*hParentLowerNum v x-(hAlphaNum v+hBetaNum v)*12*(hBase v x)^2*hVacancyDen v x)*
    (1-v)*eLogDen x+24*(hGammaNum v-hDeltaNum v)*(1-v)*(hBase v x)^3*hVacancyDen v x*eLogDen x-
    2*hProbNum v x*hUpperNum v x*hParentLowerNum v x

def h_R_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_H_r6_endpoint_R)

def h_R_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(612368384000000000000), 1⟩) (.add (.add (.mul (.mul (.mul sampleProb (.add (.mul (.const ⟨(2), 1⟩) batchParentLower) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.add batchAlpha sampleBeta) (.const ⟨(12), 1⟩)) (.pow sampleBase 2)) batchVacancy)))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) batchLogDen) (.mul (.mul (.mul (.mul (.mul (.const ⟨(24), 1⟩) (.add batchGamma (.mul (.const ⟨(-1), 1⟩) sampleDelta))) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow sampleBase 3)) batchVacancy) batchLogDen)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.const ⟨(2), 1⟩) sampleProb) batchUpper) batchParentLower))))

set_option maxRecDepth 4096 in
theorem h_R_numerator_identity_coefficients_check : PolynomialExpr.check h_R_numerator_identity_left_expression h_R_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem h_R_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_endpoint_R v x = (612368384000000000000/1 : ℝ)*hRNum v x := by
  have h := PolynomialExpr.check_sound _ _ h_R_numerator_identity_coefficients_check v x
  simpa only [h_R_numerator_identity_left_expression, h_R_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, batchAlpha_value, batchGamma_value, batchLogDen_value, batchParentLower_value, batchUpper_value, batchVacancy_value, sampleBase_value, sampleBeta_value, sampleDelta_value, sampleProb_value, hRNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def h_R_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(-635168083673088000000000000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 2)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(9), 1⟩) (.pow .activity 2)) (.const ⟨(1), 28⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(33), 1⟩) .activity) (.const ⟨(1), 14⟩)))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(121), 28⟩))) 1)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1))

def h_R_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(612368384000000000000), 1⟩) (.mul (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow sampleBase 3)) batchVacancy) batchLogDen))

set_option maxRecDepth 4096 in
theorem h_R_denominator_identity_coefficients_check : PolynomialExpr.check h_R_denominator_identity_left_expression h_R_denominator_identity_right_expression = true := by
  decide +kernel

theorem h_R_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_R_denominator v x =
      (612368384000000000000/1 : ℝ)*(12*(1-v)^2*(hBase v x)^3*hVacancyDen v x*eLogDen x) := by
  rw [dh_record_H_r6_endpoint_R_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ h_R_denominator_identity_coefficients_check v x
  simpa only [h_R_denominator_identity_left_expression, h_R_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, batchVacancy_value, batchLogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_H_R_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_endpoint_R v x =
      eProbabilityX (hActivity v) x *
        (2*dhParentUpperX .H (hActivity v) x (dhVacancyX (hActivity v) x)-
          alpha .H (hActivity v)-beta .H (hActivity v))+
      2*(gamma .H (hActivity v)-delta .H (hActivity v)-
        eProbabilityX (hActivity v) x*parentLogUpper .H (hActivity v) x*
          dhParentUpperX .H (hActivity v) x (dhVacancyX (hActivity v) x)) := by
  obtain ⟨hq, _, hB, hS⟩ := h_coordinate_denominators v x hv hx
  have hT := h_log_denominator_nonzero x hx.1
  rw [h_probability_coordinate v x hq hB, h_alpha_coordinate v hq,
    h_beta_coordinate v hq, h_delta_coordinate v hq, h_gamma_coordinate v hq,
    h_parent_lower_coordinate v x hq hB hS, h_upper_coordinate v x hq hT]
  rw [dh_R_clear _ _ _ _ _ _ _ _ _ _ _ hq hB hS hT]
  change dh_record_H_r6_endpoint_R v x = hRNum v x/(12*(1-v)^2*(hBase v x)^3*hVacancyDen v x*eLogDen x)
  unfold dh_record_H_r6_endpoint_R
  rw [h_R_numerator_identity, h_R_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (612368384000000000000/1 : ℝ) ≠ 0)

theorem h_R_guard_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < eProbabilityX lam x *
      (2*dhParentUpperX .H lam x (dhVacancyX lam x)-alpha .H lam-beta .H lam)+
      2*(gamma .H lam-delta .H lam-eProbabilityX lam x*parentLogUpper .H lam x*
        dhParentUpperX .H lam x (dhVacancyX lam x)) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_R_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_endpoint_R_positive _ x hv hx

end F4Heavy.Analysis
