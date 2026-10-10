module

public import F4Heavy.Analysis.HLowerWPiece1_0
public import F4Heavy.Analysis.HLowerWPiece1_1
public import F4Heavy.Analysis.HLowerWPiece1_2
public import F4Heavy.Analysis.HLowerWPiece1_3
public import F4Heavy.Finite.Reconstruction.Function33

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hLW1Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients hLW1Piece0Data) (realCoefficients hLW1Piece1Data)) (realCoefficients hLW1Piece2Data)) (realCoefficients hLW1Piece3Data))

theorem h_LW1_combined_value (v x : ℝ) :
    realMatrixValue hLW1Combined v x = matrixValue hLW1Piece0Data v x+
      matrixValue hLW1Piece1Data v x+matrixValue hLW1Piece2Data v x+matrixValue hLW1Piece3Data v x := by
  unfold hLW1Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def h_LW1_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(11999841207128686592000000000000000000000000000000000000000000), 9⟩ (.add (.add (.add (.matrix hLW1Piece0Data) (.matrix hLW1Piece1Data)) (.matrix hLW1Piece2Data)) (.matrix hLW1Piece3Data)))

set_option maxRecDepth 4096 in
theorem h_LW1_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_H_r6_0_1_V0) h_LW1_coefficient_identity_expression = true := by
  decide +kernel

theorem h_LW1_coefficient_identity :
    realCoefficients numerator_H_r6_0_1_V0 = realMatrixScale (11999841207128686592000000000000000000000000000000000000000000/9 : ℝ) hLW1Combined := by
  have h := CoefficientExpr.check_sound _ _ h_LW1_coefficient_identity_check
  simpa only [h_LW1_coefficient_identity_expression, CoefficientExpr.value, hLW1Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
