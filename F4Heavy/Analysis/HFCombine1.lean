module

public import F4Heavy.Analysis.HFPiece1_0
public import F4Heavy.Analysis.HFPiece1_1
public import F4Heavy.Analysis.HFPiece1_2
public import F4Heavy.Analysis.HFPiece1_3
public import F4Heavy.Analysis.HFPiece1_4
public import F4Heavy.Analysis.HFPiece1_5
public import F4Heavy.Finite.Reconstruction.Function40
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hF1Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients hF1Piece0Data) (realCoefficients hF1Piece1Data)) (realCoefficients hF1Piece2Data)) (realCoefficients hF1Piece3Data)) (realCoefficients hF1Piece4Data)) (realCoefficients hF1Piece5Data))

theorem h_F1_combined_value (v x : ℝ) :
    realMatrixValue hF1Combined v x = matrixValue hF1Piece0Data v x+
      matrixValue hF1Piece1Data v x+matrixValue hF1Piece2Data v x+
      matrixValue hF1Piece3Data v x+matrixValue hF1Piece4Data v x+matrixValue hF1Piece5Data v x := by
  unfold hF1Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def h_F1_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(5999920603564343296000000000000000000000000000000000000000000), 27⟩ (.add (.add (.add (.add (.add (.matrix hF1Piece0Data) (.matrix hF1Piece1Data)) (.matrix hF1Piece2Data)) (.matrix hF1Piece3Data)) (.matrix hF1Piece4Data)) (.matrix hF1Piece5Data)))

set_option maxRecDepth 4096 in
theorem h_F1_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_H_r6_endpoint_F1) h_F1_coefficient_identity_expression = true := by
  decide +kernel

theorem h_F1_coefficient_identity :
    realCoefficients numerator_H_r6_endpoint_F1 = realMatrixScale (5999920603564343296000000000000000000000000000000000000000000/27 : ℝ) hF1Combined := by
  have h := CoefficientExpr.check_sound _ _ h_F1_coefficient_identity_check
  simpa only [h_F1_coefficient_identity_expression, CoefficientExpr.value, hF1Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
