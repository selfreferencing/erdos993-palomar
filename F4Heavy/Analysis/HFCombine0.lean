module

public import F4Heavy.Analysis.HFPiece0_0
public import F4Heavy.Analysis.HFPiece0_1
public import F4Heavy.Analysis.HFPiece0_2
public import F4Heavy.Analysis.HFPiece0_3
public import F4Heavy.Analysis.HFPiece0_4
public import F4Heavy.Analysis.HFPiece0_5
public import F4Heavy.Finite.Reconstruction.Function39
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hF0Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients hF0Piece0Data) (realCoefficients hF0Piece1Data)) (realCoefficients hF0Piece2Data)) (realCoefficients hF0Piece3Data)) (realCoefficients hF0Piece4Data)) (realCoefficients hF0Piece5Data))

theorem h_F0_combined_value (v x : ℝ) :
    realMatrixValue hF0Combined v x = matrixValue hF0Piece0Data v x+
      matrixValue hF0Piece1Data v x+matrixValue hF0Piece2Data v x+
      matrixValue hF0Piece3Data v x+matrixValue hF0Piece4Data v x+matrixValue hF0Piece5Data v x := by
  unfold hF0Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def h_F0_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(281474976710656000000000000000000000000000000000000000000), 3⟩ (.add (.add (.add (.add (.add (.matrix hF0Piece0Data) (.matrix hF0Piece1Data)) (.matrix hF0Piece2Data)) (.matrix hF0Piece3Data)) (.matrix hF0Piece4Data)) (.matrix hF0Piece5Data)))

set_option maxRecDepth 4096 in
theorem h_F0_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_H_r6_endpoint_F0) h_F0_coefficient_identity_expression = true := by
  decide +kernel

theorem h_F0_coefficient_identity :
    realCoefficients numerator_H_r6_endpoint_F0 = realMatrixScale (281474976710656000000000000000000000000000000000000000000/3 : ℝ) hF0Combined := by
  have h := CoefficientExpr.check_sound _ _ h_F0_coefficient_identity_check
  simpa only [h_F0_coefficient_identity_expression, CoefficientExpr.value, hF0Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
