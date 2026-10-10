module

public import F4Heavy.Analysis.DFPiece0_0
public import F4Heavy.Analysis.DFPiece0_1
public import F4Heavy.Analysis.DFPiece0_2
public import F4Heavy.Analysis.DFPiece0_3
public import F4Heavy.Analysis.DFPiece0_4
public import F4Heavy.Analysis.DFPiece0_5
public import F4Heavy.Finite.Reconstruction.Function10
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dF0Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients dF0Piece0Data) (realCoefficients dF0Piece1Data)) (realCoefficients dF0Piece2Data)) (realCoefficients dF0Piece3Data)) (realCoefficients dF0Piece4Data)) (realCoefficients dF0Piece5Data))

theorem d_F0_combined_value (v x : ℝ) :
    realMatrixValue dF0Combined v x = matrixValue dF0Piece0Data v x+
      matrixValue dF0Piece1Data v x+matrixValue dF0Piece2Data v x+
      matrixValue dF0Piece3Data v x+matrixValue dF0Piece4Data v x+matrixValue dF0Piece5Data v x := by
  unfold dF0Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def d_F0_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(18897856102400000000000000000000000000000000000000000000), 9⟩ (.add (.add (.add (.add (.add (.matrix dF0Piece0Data) (.matrix dF0Piece1Data)) (.matrix dF0Piece2Data)) (.matrix dF0Piece3Data)) (.matrix dF0Piece4Data)) (.matrix dF0Piece5Data)))

set_option maxRecDepth 4096 in
theorem d_F0_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_D_r6_endpoint_F0) d_F0_coefficient_identity_expression = true := by
  decide +kernel

theorem d_F0_coefficient_identity :
    realCoefficients numerator_D_r6_endpoint_F0 = realMatrixScale (18897856102400000000000000000000000000000000000000000000/9 : ℝ) dF0Combined := by
  have h := CoefficientExpr.check_sound _ _ d_F0_coefficient_identity_check
  simpa only [d_F0_coefficient_identity_expression, CoefficientExpr.value, dF0Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
