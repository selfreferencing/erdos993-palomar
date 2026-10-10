module

public import F4Heavy.Analysis.DFPiece1_0
public import F4Heavy.Analysis.DFPiece1_1
public import F4Heavy.Analysis.DFPiece1_2
public import F4Heavy.Analysis.DFPiece1_3
public import F4Heavy.Analysis.DFPiece1_4
public import F4Heavy.Analysis.DFPiece1_5
public import F4Heavy.Finite.Reconstruction.Function11
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dF1Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients dF1Piece0Data) (realCoefficients dF1Piece1Data)) (realCoefficients dF1Piece2Data)) (realCoefficients dF1Piece3Data)) (realCoefficients dF1Piece4Data)) (realCoefficients dF1Piece5Data))

theorem d_F1_combined_value (v x : ℝ) :
    realMatrixValue dF1Combined v x = matrixValue dF1Piece0Data v x+
      matrixValue dF1Piece1Data v x+matrixValue dF1Piece2Data v x+
      matrixValue dF1Piece3Data v x+matrixValue dF1Piece4Data v x+matrixValue dF1Piece5Data v x := by
  unfold dF1Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def d_F1_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(27086067353639714816000000000000000000000000000000000000000000), 9⟩ (.add (.add (.add (.add (.add (.matrix dF1Piece0Data) (.matrix dF1Piece1Data)) (.matrix dF1Piece2Data)) (.matrix dF1Piece3Data)) (.matrix dF1Piece4Data)) (.matrix dF1Piece5Data)))

set_option maxRecDepth 4096 in
theorem d_F1_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_D_r6_endpoint_F1) d_F1_coefficient_identity_expression = true := by
  decide +kernel

theorem d_F1_coefficient_identity :
    realCoefficients numerator_D_r6_endpoint_F1 = realMatrixScale (27086067353639714816000000000000000000000000000000000000000000/9 : ℝ) dF1Combined := by
  have h := CoefficientExpr.check_sound _ _ d_F1_coefficient_identity_check
  simpa only [d_F1_coefficient_identity_expression, CoefficientExpr.value, dF1Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
