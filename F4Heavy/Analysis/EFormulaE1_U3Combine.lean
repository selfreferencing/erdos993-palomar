module

public import F4Heavy.Analysis.EFormulaE1_U3Piece0
public import F4Heavy.Analysis.EFormulaE1_U3Piece1
public import F4Heavy.Analysis.EFormulaE1_U3Piece2
public import F4Heavy.Analysis.EFormulaE1_U3Piece3
public import F4Heavy.Analysis.EFormulaE1_U3Piece4
public import F4Heavy.Finite.Reconstruction.Function19
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

noncomputable def e_record_E1_U3_combined : List (List ℝ) :=
  realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients e_record_E1_U3_piece0Data) (realCoefficients e_record_E1_U3_piece1Data)) (realCoefficients e_record_E1_U3_piece2Data)) (realCoefficients e_record_E1_U3_piece3Data)) (realMatrixScale (-1) (realCoefficients e_record_E1_U3_piece4Data))

theorem e_record_E1_U3_combined_value (lam x : ℝ) :
    realMatrixValue e_record_E1_U3_combined lam x =
      e_record_E1_U3_piece0 lam x+e_record_E1_U3_piece1 lam x+e_record_E1_U3_piece2 lam x+
        e_record_E1_U3_piece3 lam x-e_record_E1_U3_piece4 lam x := by
  unfold e_record_E1_U3_combined
  rw [realMatrixValue_add _ _ lam x (by rfl), realMatrixValue_add _ _ lam x (by rfl),
    realMatrixValue_add _ _ lam x (by rfl), realMatrixValue_add _ _ lam x (by rfl),
    realMatrixValue_scale]
  simp only [realMatrixValue_coefficients]
  change e_record_E1_U3_piece0 lam x+e_record_E1_U3_piece1 lam x+e_record_E1_U3_piece2 lam x+
    e_record_E1_U3_piece3 lam x+(-1)*e_record_E1_U3_piece4 lam x = _
  ring

def e_record_E1_U3_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(156635498240585131622400000000000000000000000000000), 9⟩ (.add (.add (.add (.add (.matrix e_record_E1_U3_piece0Data) (.matrix e_record_E1_U3_piece1Data)) (.matrix e_record_E1_U3_piece2Data)) (.matrix e_record_E1_U3_piece3Data)) (.scale ⟨(-1), 1⟩ (.matrix e_record_E1_U3_piece4Data))))

set_option maxRecDepth 4096 in
theorem e_record_E1_U3_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_E1_r8_U3) e_record_E1_U3_coefficient_identity_expression = true := by
  decide +kernel

theorem e_record_E1_U3_coefficient_identity :
    realCoefficients numerator_E1_r8_U3 = realMatrixScale (156635498240585131622400000000000000000000000000000/9) e_record_E1_U3_combined := by
  have h := CoefficientExpr.check_sound _ _ e_record_E1_U3_coefficient_identity_check
  simpa only [e_record_E1_U3_coefficient_identity_expression, CoefficientExpr.value, e_record_E1_U3_combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
