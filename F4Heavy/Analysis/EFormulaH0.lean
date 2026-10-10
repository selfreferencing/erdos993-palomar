module

public import F4Heavy.Analysis.EDenominators
public import F4Heavy.Analysis.EFormulaClearing

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def e_record_E1_H0_numerator_left_expression : PolynomialExpr :=
  (.matrix numerator_E1_r8_H0)

def e_record_E1_H0_numerator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(2573475684286464000000000000), 9⟩) (.add (.mul (.mul (.mul (.const ⟨(4), 1⟩) (.add (.mul (.mul (.add reflectE1Gamma (.mul (.const ⟨(-1), 1⟩) reflectE1Delta)) (.pow reflectEBase 2)) reflectELogDen) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .activity .parent) reflectE1Upper) reflectE1Parent)))) (.add (.add (.mul (.mul reflectE1Alpha (.add (.const ⟨(1), 1⟩) .activity)) reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 1⟩) .activity) reflectE1Parent))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(9), 16⟩) reflectE1K)))) (.add (.const ⟨(1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.mul .activity .parent) reflectE1Lower) (.pow (.add (.mul (.const ⟨(2), 1⟩) reflectE1Parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectE1Alpha reflectE1Beta) reflectEBase))) 2)) (.add (.const ⟨(1), 1⟩) .activity)) reflectELogDen))))

set_option maxRecDepth 4096 in
theorem e_record_E1_H0_numerator_coefficients_check : PolynomialExpr.check e_record_E1_H0_numerator_left_expression e_record_E1_H0_numerator_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E1_H0_numerator (lam x : ℝ) :
    matrixValue numerator_E1_r8_H0 lam x =
      (2573475684286464000000000000/9 : ℝ)*eH0Numerator .E1 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E1_H0_numerator_coefficients_check lam x
  simpa only [e_record_E1_H0_numerator_left_expression, e_record_E1_H0_numerator_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectE1Alpha_value, reflectE1Beta_value, reflectE1Delta_value, reflectE1Gamma_value, reflectE1K_value, reflectE1Lower_value, reflectE1Parent_value, reflectE1Upper_value, reflectEBase_value, reflectELogDen_value, eH0Numerator, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def e_record_E1_H0_denominator_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(2573475684286464000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.mul .activity .parent) .activity) (.const ⟨(1), 1⟩)) 3)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1))

def e_record_E1_H0_denominator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(2573475684286464000000000000), 9⟩) (.mul (.mul (.mul (.add (.const ⟨(1), 1⟩) .activity) (.pow reflectEBase 3)) reflectELogDen) (.add (.const ⟨(1), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem e_record_E1_H0_denominator_coefficients_check : PolynomialExpr.check e_record_E1_H0_denominator_left_expression e_record_E1_H0_denominator_right_expression = true := by
  decide +kernel

theorem e_record_E1_H0_denominator (lam x : ℝ) :
    polynomialValue e_record_E1_r8_H0_denominator lam x =
      (2573475684286464000000000000/9 : ℝ)*((1+lam)*(eBaseDen lam x)^3*eLogDen x*(1+x)) := by
  rw [e_record_E1_r8_H0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ e_record_E1_H0_denominator_coefficients_check lam x
  simpa only [e_record_E1_H0_denominator_left_expression, e_record_E1_H0_denominator_right_expression, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem e_record_E1_H0_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E1_r8_H0 lam x = eH0Formula .E1 lam x := by
  rw [eH0Formula_quotient .E1 lam x hlam hx]
  unfold e_record_E1_r8_H0
  rw [e_record_E1_H0_numerator, e_record_E1_H0_denominator]
  exact mul_div_mul_left _ _ (by norm_num : (2573475684286464000000000000/9 : ℝ) ≠ 0)

def e_record_E2_H0_numerator_left_expression : PolynomialExpr :=
  (.matrix numerator_E2_r8_H0)

def e_record_E2_H0_numerator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(1751047034023968768000000000000), 9⟩) (.add (.mul (.mul (.mul (.const ⟨(4), 1⟩) (.add (.mul (.mul (.add reflectE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectE2Delta)) (.pow reflectEBase 2)) reflectELogDen) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .activity .parent) reflectE2Upper) reflectE2Parent)))) (.add (.add (.mul (.mul reflectE2Alpha (.add (.const ⟨(1), 1⟩) .activity)) reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 1⟩) .activity) reflectE2Parent))) (.mul (.const ⟨(-1), 1⟩) (.mul (.const ⟨(9), 16⟩) reflectE2K)))) (.add (.const ⟨(1), 1⟩) .parent)) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul (.mul (.mul .activity .parent) reflectE2Lower) (.pow (.add (.mul (.const ⟨(2), 1⟩) reflectE2Parent) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectE2Alpha reflectE2Beta) reflectEBase))) 2)) (.add (.const ⟨(1), 1⟩) .activity)) reflectELogDen))))

set_option maxRecDepth 4096 in
theorem e_record_E2_H0_numerator_coefficients_check : PolynomialExpr.check e_record_E2_H0_numerator_left_expression e_record_E2_H0_numerator_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E2_H0_numerator (lam x : ℝ) :
    matrixValue numerator_E2_r8_H0 lam x =
      (1751047034023968768000000000000/9 : ℝ)*eH0Numerator .E2 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E2_H0_numerator_coefficients_check lam x
  simpa only [e_record_E2_H0_numerator_left_expression, e_record_E2_H0_numerator_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectE2Alpha_value, reflectE2Beta_value, reflectE2Delta_value, reflectE2Gamma_value, reflectE2K_value, reflectE2Lower_value, reflectE2Parent_value, reflectE2Upper_value, reflectEBase_value, reflectELogDen_value, eH0Numerator, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h


def e_record_E2_H0_denominator_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(1751047034023968768000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.mul .activity .parent) .activity) (.const ⟨(1), 1⟩)) 3)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1))

def e_record_E2_H0_denominator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(1751047034023968768000000000000), 9⟩) (.mul (.mul (.mul (.add (.const ⟨(1), 1⟩) .activity) (.pow reflectEBase 3)) reflectELogDen) (.add (.const ⟨(1), 1⟩) .parent)))

set_option maxRecDepth 4096 in
theorem e_record_E2_H0_denominator_coefficients_check : PolynomialExpr.check e_record_E2_H0_denominator_left_expression e_record_E2_H0_denominator_right_expression = true := by
  decide +kernel

theorem e_record_E2_H0_denominator (lam x : ℝ) :
    polynomialValue e_record_E2_r8_H0_denominator lam x =
      (1751047034023968768000000000000/9 : ℝ)*((1+lam)*(eBaseDen lam x)^3*eLogDen x*(1+x)) := by
  rw [e_record_E2_r8_H0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ e_record_E2_H0_denominator_coefficients_check lam x
  simpa only [e_record_E2_H0_denominator_left_expression, e_record_E2_H0_denominator_right_expression, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem e_record_E2_H0_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E2_r8_H0 lam x = eH0Formula .E2 lam x := by
  rw [eH0Formula_quotient .E2 lam x hlam hx]
  unfold e_record_E2_r8_H0
  rw [e_record_E2_H0_numerator, e_record_E2_H0_denominator]
  exact mul_div_mul_left _ _ (by norm_num : (1751047034023968768000000000000/9 : ℝ) ≠ 0)

theorem eH0Formula_positive (r : Row) (lam x : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < eH0Formula r lam x := by
  have hl := (inRow_activity_pos r lam hr).le
  have hx0 : 0 ≤ x := by linarith only [hx.1]
  rcases he with rfl | rfl
  · rw [← e_record_E1_H0_formula lam x hl hx0]
    exact e_record_E1_r8_H0_positive lam x hr hx
  · rw [← e_record_E2_H0_formula lam x hl hx0]
    exact e_record_E2_r8_H0_positive lam x hr hx

theorem e_original_virtual_discriminant_positive (r : Row) (lam Y : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ parentX lam Y ∧ parentX lam Y ≤ 1) :
    0 < 4*(gamma r lam-delta r lam-p lam Y*parentLogUpper r lam (parentX lam Y)*eParentBase r lam Y)*
      tangentN r lam Y 0 (3/4) (eParentBase r lam Y) -
      p lam Y*parentLogLower r lam (parentX lam Y)*(2*eParentBase r lam Y-alpha r lam-beta r lam)^2 := by
  rw [← eH0Formula_original r lam Y (inRow_activity_pos r lam hr)]
  exact eH0Formula_positive r lam (parentX lam Y) he hr hx

end F4Heavy.Analysis
