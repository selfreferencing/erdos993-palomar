module

public import F4Heavy.Analysis.EFormulaUCore
public import F4Heavy.Analysis.ESupportData
public import F4Heavy.Analysis.EDenominators

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def e_record_E1_U0_numerator_left_expression : PolynomialExpr :=
  (.mul (.matrix numerator_E1_r8_U0) (.pow reflectEBase 2))

def e_record_E1_U0_numerator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(519055607465602570898531942400000000000000000000000000000000000), 9⟩) (.add (.add (.mul (.mul (.const ⟨(4), 1⟩) (.add (.mul (.mul reflectE1Delta (.pow reflectEBase 2)) reflectELogDen) (.mul (.add (.mul (.mul (.add reflectE1Gamma (.mul (.const ⟨(-1), 1⟩) reflectE1Delta)) (.pow reflectEBase 2)) reflectELogDen) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .activity .parent) reflectE1Upper) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))))) reflectE1Height0))) (.add (.mul (.mul (.mul .activity .parent) (.add (.mul (.const ⟨(15), 16⟩) reflectE1K) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 1⟩) .activity) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent))))))) (.add (.const ⟨(1), 1⟩) .parent)) (.mul (.mul (.mul (.mul (.mul reflectE1Lower (.mul .activity .parent)) reflectE1Beta) reflectE1Vertex0) (.add (.const ⟨(1), 1⟩) .activity)) reflectEBase))) (.mul (.mul (.mul (.mul (.mul (.const ⟨(4), 1⟩) reflectE1Delta) reflectE1Lower) (.add (.mul (.mul (.mul (.mul .activity .parent) (.add (.mul (.const ⟨(2), 1⟩) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectE1Alpha reflectE1Beta) reflectEBase)))) reflectELogDen) reflectE1Vertex0) (.mul (.add (.mul (.mul (.add reflectE1Gamma (.mul (.const ⟨(-1), 1⟩) reflectE1Delta)) (.pow reflectEBase 2)) reflectELogDen) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .activity .parent) reflectE1Upper) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))))) (.pow reflectE1Vertex0 2)))) (.add (.const ⟨(1), 1⟩) .activity)) (.pow reflectEBase 2))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul reflectE1Lower reflectE1Height0) (.pow (.mul (.mul .activity .parent) (.add (.mul (.const ⟨(2), 1⟩) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectE1Alpha reflectE1Beta) reflectEBase)))) 2)) (.add (.const ⟨(1), 1⟩) .activity)) reflectELogDen))))

set_option maxRecDepth 4096 in
theorem e_record_E1_U0_numerator_coefficients_check : PolynomialExpr.check e_record_E1_U0_numerator_left_expression e_record_E1_U0_numerator_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E1_U0_numerator (lam x : ℝ) :
    matrixValue numerator_E1_r8_U0 lam x*(eBaseDen lam x)^2 =
      (519055607465602570898531942400000000000000000000000000000000000/9 : ℝ)*(eUNumerator .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0)) := by
  have h := PolynomialExpr.check_sound _ _ e_record_E1_U0_numerator_coefficients_check lam x
  simpa only [e_record_E1_U0_numerator_left_expression, e_record_E1_U0_numerator_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectE1Alpha_value, reflectE1Beta_value, reflectE1Delta_value, reflectE1Gamma_value, reflectE1Height0_value, reflectE1K_value, reflectE1Lower_value, reflectE1Parent_value, reflectE1Upper_value, reflectE1Vertex0_value, reflectEBase_value, reflectELogDen_value, eUNumerator, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def e_record_E1_U0_denominator_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(519055607465602570898531942400000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.mul .activity .parent) .activity) (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1)) (.pow reflectEBase 2))

def e_record_E1_U0_denominator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(519055607465602570898531942400000000000000000000000000000000000), 9⟩) (.mul (.mul (.mul (.add (.const ⟨(1), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) .activity)) (.pow reflectEBase 4)) reflectELogDen))

set_option maxRecDepth 4096 in
theorem e_record_E1_U0_denominator_coefficients_check : PolynomialExpr.check e_record_E1_U0_denominator_left_expression e_record_E1_U0_denominator_right_expression = true := by
  decide +kernel

theorem e_record_E1_U0_denominator (lam x : ℝ) :
    polynomialValue e_record_E1_r8_U0_denominator lam x*(eBaseDen lam x)^2 =
      (519055607465602570898531942400000000000000000000000000000000000/9 : ℝ)*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by
  rw [e_record_E1_r8_U0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ e_record_E1_U0_denominator_coefficients_check lam x
  simpa only [e_record_E1_U0_denominator_left_expression, e_record_E1_U0_denominator_right_expression, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem e_record_E1_U0_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E1_r8_U0 lam x = eUFormula .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0) := by
  rw [eUFormula_quotient _ _ _ _ _ hlam hx]
  unfold e_record_E1_r8_U0
  have hB : 0 < eBaseDen lam x := by unfold eBaseDen; positivity
  have hT : 0 < eLogDen x := by unfold eLogDen; positivity
  apply (div_eq_div_iff (ne_of_gt (e_record_E1_r8_U0_denominator_positive lam x hlam hx))
    (by positivity : (1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x ≠ 0)).mpr
  apply mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt hB))
  calc
    (matrixValue numerator_E1_r8_U0 lam x*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x))*(eBaseDen lam x)^2 =
        (matrixValue numerator_E1_r8_U0 lam x*(eBaseDen lam x)^2)*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by ring
    _ = ((519055607465602570898531942400000000000000000000000000000000000/9 : ℝ)*(eUNumerator .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0)))*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by rw [e_record_E1_U0_numerator]
    _ = (eUNumerator .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0))*(polynomialValue e_record_E1_r8_U0_denominator lam x*(eBaseDen lam x)^2) := by
      rw [e_record_E1_U0_denominator]
      ring
    _ = ((eUNumerator .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0))*polynomialValue e_record_E1_r8_U0_denominator lam x)*(eBaseDen lam x)^2 := by ring

theorem e_record_E1_U0_formula_positive (lam x : ℝ)
    (hlam : (13/10 : ℝ) ≤ lam ∧ lam ≤ (29/20 : ℝ))
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < eUFormula .E1 lam x (eSupportVertex .E1 lam 0) (eSupportHeight .E1 lam 0) := by
  rw [← e_record_E1_U0_formula lam x (by linarith only [hlam.1]) (by linarith only [hx.1])]
  exact e_record_E1_r8_U0_positive lam x hlam hx

end F4Heavy.Analysis
