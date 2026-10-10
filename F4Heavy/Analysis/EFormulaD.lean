module

public import F4Heavy.Analysis.EDenominators
public import F4Heavy.Analysis.EFormulaCore

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def e_record_E1_D_numerator_left_expression : PolynomialExpr :=
  (.matrix numerator_E1_r8_D)

def e_record_E1_D_numerator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(654468710400000000000), 9⟩) (.add (.mul (.mul (.mul .activity .parent) reflectE1Upper) (.add (.add reflectE1Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.add reflectE1Gamma (.mul (.const ⟨(-1), 1⟩) reflectE1Delta)) (.pow reflectEBase 2)) reflectELogDen))))

set_option maxRecDepth 4096 in
theorem e_record_E1_D_numerator_coefficients_check : PolynomialExpr.check e_record_E1_D_numerator_left_expression e_record_E1_D_numerator_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E1_D_numerator (lam x : ℝ) :
    matrixValue numerator_E1_r8_D lam x = (654468710400000000000/9 : ℝ)*eDNumerator .E1 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E1_D_numerator_coefficients_check lam x
  simpa only [e_record_E1_D_numerator_left_expression, e_record_E1_D_numerator_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectE1Delta_value, reflectE1Gamma_value, reflectE1Parent_value, reflectE1Upper_value, reflectEBase_value, reflectELogDen_value, eDNumerator, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h

theorem e_record_E1_D_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E1_r8_D lam x = eDFormula .E1 lam x := by
  rw [eDFormula_quotient .E1 lam x hlam hx]
  unfold e_record_E1_r8_D
  rw [e_record_E1_D_numerator, e_record_E1_r8_D_denominator_value]
  have hd : (654468710400000000000 : ℝ)*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 =
      (654468710400000000000/9 : ℝ)*((eBaseDen lam x)^2*eLogDen x) := by
    unfold eBaseDen eLogDen
    ring
  rw [hd]
  exact mul_div_mul_left _ _ (by norm_num : (654468710400000000000/9 : ℝ) ≠ 0)


def e_record_E2_D_numerator_left_expression : PolynomialExpr :=
  (.matrix numerator_E2_r8_D)

def e_record_E2_D_numerator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(6958035763200000000000), 9⟩) (.add (.mul (.mul (.mul .activity .parent) reflectE2Upper) (.add (.add reflectE2Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.add reflectE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectE2Delta)) (.pow reflectEBase 2)) reflectELogDen))))

set_option maxRecDepth 4096 in
theorem e_record_E2_D_numerator_coefficients_check : PolynomialExpr.check e_record_E2_D_numerator_left_expression e_record_E2_D_numerator_right_expression = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E2_D_numerator (lam x : ℝ) :
    matrixValue numerator_E2_r8_D lam x = (6958035763200000000000/9 : ℝ)*eDNumerator .E2 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E2_D_numerator_coefficients_check lam x
  simpa only [e_record_E2_D_numerator_left_expression, e_record_E2_D_numerator_right_expression, PolynomialExpr.value, PolynomialExpr.matrix_value, reflectE2Delta_value, reflectE2Gamma_value, reflectE2Parent_value, reflectE2Upper_value, reflectEBase_value, reflectELogDen_value, eDNumerator, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, sub_eq_add_neg, neg_mul, one_mul] using h

theorem e_record_E2_D_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E2_r8_D lam x = eDFormula .E2 lam x := by
  rw [eDFormula_quotient .E2 lam x hlam hx]
  unfold e_record_E2_r8_D
  rw [e_record_E2_D_numerator, e_record_E2_r8_D_denominator_value]
  have hd : (6958035763200000000000 : ℝ)*(lam*x+lam+1)^2*(x^2+4*x/3+1/9)^1 =
      (6958035763200000000000/9 : ℝ)*((eBaseDen lam x)^2*eLogDen x) := by
    unfold eBaseDen eLogDen
    ring
  rw [hd]
  exact mul_div_mul_left _ _ (by norm_num : (6958035763200000000000/9 : ℝ) ≠ 0)


theorem eDFormula_positive (r : Row) (lam x : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < eDFormula r lam x := by
  have hl := (inRow_activity_pos r lam hr).le
  have hx0 : 0 ≤ x := by linarith only [hx.1]
  rcases he with rfl | rfl
  · rw [← e_record_E1_D_formula lam x hl hx0]
    exact e_record_E1_r8_D_positive lam x hr hx
  · rw [← e_record_E2_D_formula lam x hl hx0]
    exact e_record_E2_r8_D_positive lam x hr hx

theorem e_original_upper_curvature_negative (r : Row) (lam Y : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx : (1/4 : ℝ) ≤ parentX lam Y ∧ parentX lam Y ≤ 1) :
    gamma r lam-delta r lam-p lam Y*parentLogUpper r lam (parentX lam Y)*
      (eParentBase r lam Y+(1-p lam Y)) < 0 := by
  have h := eDFormula_positive r lam (parentX lam Y) he hr hx
  rw [eDFormula_original r lam Y (inRow_activity_pos r lam hr)] at h
  linarith only [h]

end F4Heavy.Analysis
