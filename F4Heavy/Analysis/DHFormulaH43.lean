module

public import F4Heavy.Analysis.DHDenominator43
public import F4Heavy.Analysis.HGuardCore

public import F4Heavy.Analysis.HIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hCurvatureNum (v x : ℝ) : ℝ :=
  hProbNum v x*hLowerNum v x*(hGammaNum v*(12*(hBase v x)^2-
    6*hProbNum v x*hBase v x-(hProbNum v x)^2)+12*(1-v)*hBase v x*(hBase v x-hProbNum v x))-
    (hGammaNum v-hDeltaNum v)*12*(1-v)*(hBase v x)^3*(1+x)

def h_curvature_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_H_r6_endpoint_D)

def h_curvature_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(8388608000000000000), 1⟩) (.add (.mul (.mul sampleProb sampleLower) (.add (.mul batchGamma (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow sampleBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) sampleProb) sampleBase))) (.mul (.const ⟨(-1), 1⟩) (.pow sampleProb 2)))) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) sampleBase) (.add sampleBase (.mul (.const ⟨(-1), 1⟩) sampleProb))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.add batchGamma (.mul (.const ⟨(-1), 1⟩) sampleDelta)) (.const ⟨(12), 1⟩)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow sampleBase 3)) (.add (.const ⟨(1), 1⟩) .parent)))))

set_option maxRecDepth 4096 in
theorem h_curvature_numerator_identity_coefficients_check : PolynomialExpr.check h_curvature_numerator_identity_left_expression h_curvature_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem h_curvature_numerator_identity (v x : ℝ) :
    matrixValue numerator_H_r6_endpoint_D v x = (8388608000000000000/1 : ℝ)*hCurvatureNum v x := by
  have h := PolynomialExpr.check_sound _ _ h_curvature_numerator_identity_coefficients_check v x
  simpa only [h_curvature_numerator_identity_left_expression, h_curvature_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, batchGamma_value, sampleBase_value, sampleDelta_value, sampleLower_value, sampleProb_value, hCurvatureNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def h_curvature_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.const ⟨(34527510528000000000000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 2)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.mul (.const ⟨(3), 1⟩) .activity) (.const ⟨(1), 7⟩))) .parent) (.const ⟨(11), 7⟩)) 3))

def h_curvature_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(8388608000000000000), 1⟩) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow sampleBase 3)) (.add (.const ⟨(1), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem h_curvature_denominator_identity_coefficients_check : PolynomialExpr.check h_curvature_denominator_identity_left_expression h_curvature_denominator_identity_right_expression = true := by
  decide +kernel

theorem h_curvature_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_H_r6_endpoint_D_denominator v x =
      (8388608000000000000/1 : ℝ)*(12*(1-v)^2*(hBase v x)^3*(1+x)) := by
  rw [dh_record_H_r6_endpoint_D_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ h_curvature_denominator_identity_coefficients_check v x
  simpa only [h_curvature_denominator_identity_left_expression, h_curvature_denominator_identity_right_expression, PolynomialExpr.value, sampleBase_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_H_curvature_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_H_r6_endpoint_D v x =
      eProbabilityX (hActivity v) x * parentLogLower .H (hActivity v) x *
        dhParentUpperX .H (hActivity v) x 1 -
      (gamma .H (hActivity v)-delta .H (hActivity v)) := by
  have hq : 1-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hC : 1+x ≠ 0 := ne_of_gt (by linarith only [hx.1])
  have hB := (h_coordinate_denominators v x hv hx).2.2.1
  unfold dhParentUpperX dhParentBaseX
  rw [h_probability_coordinate v x hq hB, h_gamma_coordinate v hq,
    h_delta_coordinate v hq, h_lower_coordinate v x hq hC]
  simp only [mul_one]
  rw [dh_curvature_clear _ _ _ _ _ _ _ hq hB hC]
  change dh_record_H_r6_endpoint_D v x = hCurvatureNum v x/(12*(1-v)^2*(hBase v x)^3*(1+x))
  unfold dh_record_H_r6_endpoint_D
  rw [h_curvature_numerator_identity, h_curvature_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (8388608000000000000/1 : ℝ) ≠ 0)

theorem h_curvature_guard_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < eProbabilityX lam x * parentLogLower .H lam x * dhParentUpperX .H lam x 1 -
      (gamma .H lam-delta .H lam) := by
  have hv := h_activity_coordinates lam hr
  have he := activity_transform_inverse (7/4 : ℝ) lam (by norm_num) (inRow_activity_pos .H lam hr)
  have hf := dh_record_H_curvature_formula ((lam-(7/4 : ℝ))/(lam+(7/4 : ℝ))) x hv hx
  unfold hActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_H_r6_endpoint_D_positive _ x hv hx

end F4Heavy.Analysis
