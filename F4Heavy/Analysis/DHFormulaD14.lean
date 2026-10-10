module

public import F4Heavy.Analysis.DHDenominator14
public import F4Heavy.Analysis.DFormulaCoordinates

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dCurvatureNum (v x : ℝ) : ℝ :=
  dProbNum v x*dLowerNum v x*(dGammaNum v*(12*(dBase v x)^2-
    6*dProbNum v x*dBase v x-(dProbNum v x)^2)+12*(1-v)*dBase v x*(dBase v x-dProbNum v x))-
    (dGammaNum v-dDeltaNum v)*12*(1-v)*(dBase v x)^3*(1+x)

def d_curvature_numerator_identity_left_expression : PolynomialExpr :=
  (.matrix numerator_D_r6_endpoint_D)

def d_curvature_numerator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(6553600000000000000), 1⟩) (.add (.mul (.mul reflectDProb reflectDLower) (.add (.mul reflectDGamma (.add (.add (.mul (.const ⟨(12), 1⟩) (.pow reflectDBase 2)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.const ⟨(6), 1⟩) reflectDProb) reflectDBase))) (.mul (.const ⟨(-1), 1⟩) (.pow reflectDProb 2)))) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) reflectDBase) (.add reflectDBase (.mul (.const ⟨(-1), 1⟩) reflectDProb))))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.add reflectDGamma (.mul (.const ⟨(-1), 1⟩) reflectDDelta)) (.const ⟨(12), 1⟩)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.pow reflectDBase 3)) (.add (.const ⟨(1), 1⟩) .parent)))))

set_option maxRecDepth 4096 in
theorem d_curvature_numerator_identity_coefficients_check : PolynomialExpr.check d_curvature_numerator_identity_left_expression d_curvature_numerator_identity_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem d_curvature_numerator_identity (v x : ℝ) :
    matrixValue numerator_D_r6_endpoint_D v x = 6553600000000000000*dCurvatureNum v x := by
  have h := PolynomialExpr.check_sound _ _ d_curvature_numerator_identity_coefficients_check v x
  simpa only [d_curvature_numerator_identity_left_expression, d_curvature_numerator_identity_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectDBase_value, reflectDDelta_value, reflectDGamma_value, reflectDLower_value, reflectDProb_value, dCurvatureNum, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def d_curvature_denominator_identity_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.const ⟨(5033164800000000000000), 1⟩) (.pow (.add .activity (.mul (.const ⟨(-1), 1⟩) (.const ⟨(1), 1⟩))) 2)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.add (.mul .activity .parent) (.mul (.const ⟨(-1), 1⟩) (.mul .activity (.const ⟨(1), 4⟩)))) .parent) (.const ⟨(9), 4⟩)) 3))

def d_curvature_denominator_identity_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(6553600000000000000), 1⟩) (.mul (.mul (.mul (.const ⟨(12), 1⟩) (.pow (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity)) 2)) (.pow reflectDBase 3)) (.add (.const ⟨(1), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem d_curvature_denominator_identity_coefficients_check : PolynomialExpr.check d_curvature_denominator_identity_left_expression d_curvature_denominator_identity_right_expression = true := by
  decide +kernel

theorem d_curvature_denominator_identity (v x : ℝ) :
    polynomialValue dh_record_D_r6_endpoint_D_denominator v x =
      6553600000000000000*(12*(1-v)^2*(dBase v x)^3*(1+x)) := by
  rw [dh_record_D_r6_endpoint_D_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ d_curvature_denominator_identity_coefficients_check v x
  simpa only [d_curvature_denominator_identity_left_expression, d_curvature_denominator_identity_right_expression, PolynomialExpr.value, reflectDBase_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem dh_record_D_curvature_formula (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    dh_record_D_r6_endpoint_D v x =
      eProbabilityX (dActivity v) x * parentLogLower .D (dActivity v) x *
        dhParentUpperX .D (dActivity v) x 1 -
      (gamma .D (dActivity v)-delta .D (dActivity v)) := by
  have hq : 1-v ≠ 0 := ne_of_gt (by linarith only [hv.2])
  have hC : 1+x ≠ 0 := ne_of_gt (by linarith only [hx.1])
  have hB : dBase v x ≠ 0 := by
    have hs := (d_denominator_factor_signs v x hv hx).2.2.2.2.1
    unfold dBase
    apply ne_of_gt
    nlinarith only [hs]
  unfold dhParentUpperX dhParentBaseX
  rw [d_probability_coordinate v x hq hB, d_gamma_coordinate v hq,
    d_delta_coordinate v hq, d_lower_coordinate v x hq hC]
  simp only [mul_one]
  rw [dh_curvature_clear _ _ _ _ _ _ _ hq hB hC]
  change dh_record_D_r6_endpoint_D v x = dCurvatureNum v x/(12*(1-v)^2*(dBase v x)^3*(1+x))
  unfold dh_record_D_r6_endpoint_D
  rw [d_curvature_numerator_identity, d_curvature_denominator_identity]
  exact mul_div_mul_left _ _ (by norm_num : (6553600000000000000 : ℝ) ≠ 0)

theorem d_curvature_guard_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < eProbabilityX lam x * parentLogLower .D lam x * dhParentUpperX .D lam x 1 -
      (gamma .D lam-delta .D lam) := by
  have hv := d_activity_coordinates lam hr
  have he := activity_transform_inverse (4/5 : ℝ) lam (by norm_num) (inRow_activity_pos .D lam hr)
  have hf := dh_record_D_curvature_formula ((lam-(4/5 : ℝ))/(lam+(4/5 : ℝ))) x hv hx
  unfold dActivity at hf
  rw [he] at hf
  rw [← hf]
  exact dh_record_D_r6_endpoint_D_positive _ x hv hx

end F4Heavy.Analysis
