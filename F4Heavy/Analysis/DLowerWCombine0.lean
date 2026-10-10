module

public import F4Heavy.Analysis.DLowerWPiece0_0
public import F4Heavy.Analysis.DLowerWPiece0_1
public import F4Heavy.Analysis.DLowerWPiece0_2
public import F4Heavy.Analysis.DLowerWPiece0_3
public import F4Heavy.Finite.Reconstruction.Function00

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dLW0Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients dLW0Piece0Data) (realCoefficients dLW0Piece1Data)) (realCoefficients dLW0Piece2Data)) (realCoefficients dLW0Piece3Data))

theorem d_LW0_combined_value (v x : ℝ) :
    realMatrixValue dLW0Combined v x = matrixValue dLW0Piece0Data v x+
      matrixValue dLW0Piece1Data v x+matrixValue dLW0Piece2Data v x+matrixValue dLW0Piece3Data v x := by
  unfold dLW0Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def d_LW0_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(3326022674022400000000000000000000000000000000000000000), 9⟩ (.add (.add (.add (.matrix dLW0Piece0Data) (.matrix dLW0Piece1Data)) (.matrix dLW0Piece2Data)) (.matrix dLW0Piece3Data)))

set_option maxRecDepth 4096 in
theorem d_LW0_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_D_r6_0_0_V0) d_LW0_coefficient_identity_expression = true := by
  decide +kernel

theorem d_LW0_coefficient_identity :
    realCoefficients numerator_D_r6_0_0_V0 = realMatrixScale (3326022674022400000000000000000000000000000000000000000/9 : ℝ) dLW0Combined := by
  have h := CoefficientExpr.check_sound _ _ d_LW0_coefficient_identity_check
  simpa only [d_LW0_coefficient_identity_expression, CoefficientExpr.value, dLW0Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
