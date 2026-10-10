module

public import F4Heavy.Analysis.DHDenominator42
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hCNum (v x : ℝ) : ℝ :=
  240*hDeltaNum v*(hBase v x)^3*hVacancyDen v x-
    12*hProbNum v x*(2*hParentLowerNum v x-(hAlphaNum v+hBetaNum v)*12*(hBase v x)^2*hVacancyDen v x)

def h_C_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_H_r6_endpoint_C)

def h_C_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(2097152), 3⟩) (.add (.mul (.mul (.mul (.const ⟨(240), 1⟩) sampleDelta) (.pow sampleBase 3)) batchVacancy) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(12), 1⟩) sampleProb) (.add (.mul (.const ⟨(2), 1⟩) batchParentLower) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.add batchAlpha sampleBeta) (.const ⟨(12), 1⟩)) (.pow sampleBase 2)) batchVacancy)))))))

set_option maxRecDepth 4096 in
theorem h_C_numerator_identity_coefficients_check : PolynomialExpr.check h_C_numerator_identity_left_expression h_C_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem h_C_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_endpoint_C v x = (2097152/3 : ℝ)*hCNum v x := by
  have h := PolynomialExpr.check_sound _ _ h_C_numerator_identity_coefficients_check v x
  simpa only [h_C_numerator_identity_left_expression, h_C_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, batchAlpha_value, batchParentLower_value, batchVacancy_value, sampleBase_value, sampleBeta_value, sampleDelta_value, sampleProb_value, hCNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def h_C_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.const ⟨(402820956160), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3)) (.pow (.add (.add (.add (.add (.mul (.pow .activity 2) .parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(9), 1⟩) (.pow .activity 2)) (.const ⟨(1), 28⟩)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(33), 1⟩) .activity) (.const ⟨(1), 14⟩)))) (.mul (.const ⟨(-1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.const ⟨(121), 28⟩))) 1))

def h_C_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(2097152), 3⟩) (.mul (.mul (.mul (.const ⟨(60), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow sampleBase 3)) batchVacancy))

set_option maxRecDepth 4096 in
theorem h_C_denominator_identity_coefficients_check : PolynomialExpr.check h_C_denominator_identity_left_expression h_C_denominator_identity_right_expression = true := by
  decide +kernel

theorem h_C_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_C_denominator v x =
      (2097152/3 : ℝ)*(60*(1-v)*(hBase v x)^3*hVacancyDen v x) := by
  rw [dh_record_H_r6_endpoint_C_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ h_C_denominator_identity_coefficients_check v x
  simpa only [h_C_denominator_identity_left_expression, h_C_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, batchVacancy_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_H_C_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_endpoint_C v x =
      4*delta .H (hActivity v)-(12/5)*(eProbabilityX (hActivity v) x *
        (2*dhParentUpperX .H (hActivity v) x (dhVacancyX (hActivity v) x)-
          alpha .H (hActivity v)-beta .H (hActivity v))) := by
  obtain ⟨hq, _, hB, hS⟩ := h_coordinate_denominators v x hv hx
  rw [h_probability_coordinate v x hq hB, h_alpha_coordinate v hq,
    h_beta_coordinate v hq, h_delta_coordinate v hq, h_parent_lower_coordinate v x hq hB hS]
  rw [h_C_clear _ _ _ _ _ _ _ _ hq hB hS]
  change dh_record_H_r6_endpoint_C v x = hCNum v x/(60*(1-v)*(hBase v x)^3*hVacancyDen v x)
  unfold dh_record_H_r6_endpoint_C
  rw [h_C_numerator_identity, h_C_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (2097152/3 : ℝ) ≠ 0)

theorem h_C_guard_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < 4*delta .H lam-(12/5)*(eProbabilityX lam x *
      (2*dhParentUpperX .H lam x (dhVacancyX lam x)-alpha .H lam-beta .H lam)) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_C_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_endpoint_C_positive _ x hv hx

end F4Heavy.Analysis
