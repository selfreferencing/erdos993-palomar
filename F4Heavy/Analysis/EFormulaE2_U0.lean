module

public import F4Heavy.Analysis.EFormulaUPieces
public import F4Heavy.Analysis.ESupportData
public import F4Heavy.Analysis.EFormulaE2_U0Piece0
public import F4Heavy.Analysis.EFormulaE2_U0Piece1
public import F4Heavy.Analysis.EFormulaE2_U0Piece2
public import F4Heavy.Analysis.EFormulaE2_U0Piece3
public import F4Heavy.Analysis.EFormulaE2_U0Piece4
public import F4Heavy.Analysis.EFormulaE2_U0Combine
public import F4Heavy.Analysis.EDenominators

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem e_record_E2_U0_numerator (lam x : ℝ) :
    matrixValue numerator_E2_r8_U0 lam x*(eBaseDen lam x)^2 =
      (108327646982887723498714693632000000000000000000000000000000000000/9 : ℝ)*(eUNumerator .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0)) := by
  rw [eUNumerator_pieces, e_record_E2_U0_piece0_value, e_record_E2_U0_piece1_value, e_record_E2_U0_piece2_value, e_record_E2_U0_piece3_value, e_record_E2_U0_piece4_value]
  rw [← e_record_E2_U0_lifted_value]
  rw [← realMatrixValue_coefficients, e_record_E2_U0_coefficient_identity, realMatrixValue_scale, e_record_E2_U0_combined_value]

def e_record_E2_U0_denominator_left_expression : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.const ⟨(108327646982887723498714693632000000000000000000000000000000000000), 1⟩) (.pow (.add .activity (.const ⟨(1), 1⟩)) 1)) (.pow (.add .parent (.const ⟨(1), 1⟩)) 1)) (.pow (.add (.add (.mul .activity .parent) .activity) (.const ⟨(1), 1⟩)) 2)) (.pow (.add (.add (.pow .parent 2) (.mul (.mul (.const ⟨(4), 1⟩) .parent) (.const ⟨(1), 3⟩))) (.const ⟨(1), 9⟩)) 1)) (.pow reflectEBase 2))

def e_record_E2_U0_denominator_right_expression : PolynomialExpr :=
  (.mul (.const ⟨(108327646982887723498714693632000000000000000000000000000000000000), 9⟩) (.mul (.mul (.mul (.add (.const ⟨(1), 1⟩) .parent) (.add (.const ⟨(1), 1⟩) .activity)) (.pow reflectEBase 4)) reflectELogDen))

set_option maxRecDepth 4096 in
theorem e_record_E2_U0_denominator_coefficients_check : PolynomialExpr.check e_record_E2_U0_denominator_left_expression e_record_E2_U0_denominator_right_expression = true := by
  decide +kernel

theorem e_record_E2_U0_denominator (lam x : ℝ) :
    polynomialValue e_record_E2_r8_U0_denominator lam x*(eBaseDen lam x)^2 =
      (108327646982887723498714693632000000000000000000000000000000000000/9 : ℝ)*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by
  rw [e_record_E2_r8_U0_denominator_value]
  have hp := PolynomialExpr.check_sound _ _ e_record_E2_U0_denominator_coefficients_check lam x
  simpa only [e_record_E2_U0_denominator_left_expression, e_record_E2_U0_denominator_right_expression, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_ofNat, Nat.cast_one, div_one, sub_eq_add_neg, neg_mul, one_mul, mul_one, div_eq_mul_inv, inv_one, mul_assoc] using hp

theorem e_record_E2_U0_formula (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    e_record_E2_r8_U0 lam x = eUFormula .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0) := by
  rw [eUFormula_quotient _ _ _ _ _ hlam hx]
  unfold e_record_E2_r8_U0
  have hB : 0 < eBaseDen lam x := by unfold eBaseDen; positivity
  have hT : 0 < eLogDen x := by unfold eLogDen; positivity
  apply (div_eq_div_iff (ne_of_gt (e_record_E2_r8_U0_denominator_positive lam x hlam hx))
    (by positivity : (1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x ≠ 0)).mpr
  apply mul_right_cancel₀ (pow_ne_zero 2 (ne_of_gt hB))
  calc
    (matrixValue numerator_E2_r8_U0 lam x*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x))*(eBaseDen lam x)^2 =
        (matrixValue numerator_E2_r8_U0 lam x*(eBaseDen lam x)^2)*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by ring
    _ = ((108327646982887723498714693632000000000000000000000000000000000000/9 : ℝ)*(eUNumerator .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0)))*((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by rw [e_record_E2_U0_numerator]
    _ = (eUNumerator .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0))*(polynomialValue e_record_E2_r8_U0_denominator lam x*(eBaseDen lam x)^2) := by
      rw [e_record_E2_U0_denominator]
      ring
    _ = ((eUNumerator .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0))*polynomialValue e_record_E2_r8_U0_denominator lam x)*(eBaseDen lam x)^2 := by ring

theorem e_record_E2_U0_formula_positive (lam x : ℝ)
    (hlam : (29/20 : ℝ) ≤ lam ∧ lam ≤ (8/5 : ℝ))
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) : 0 < eUFormula .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0) := by
  rw [← e_record_E2_U0_formula lam x (by linarith only [hlam.1]) (by linarith only [hx.1])]
  exact e_record_E2_r8_U0_positive lam x hlam hx

end F4Heavy.Analysis
