module

public import F4Heavy.Analysis.DLowerWPiece1_0
public import F4Heavy.Analysis.DLowerWPiece1_1
public import F4Heavy.Analysis.DLowerWPiece1_2
public import F4Heavy.Analysis.DLowerWPiece1_3
public import F4Heavy.Finite.Reconstruction.Function05

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def dLW1Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients dLW1Piece0Data) (realCoefficients dLW1Piece1Data)) (realCoefficients dLW1Piece2Data)) (realCoefficients dLW1Piece3Data))

theorem d_LW1_combined_value (v x : ℝ) :
    realMatrixValue dLW1Combined v x = matrixValue dLW1Piece0Data v x+
      matrixValue dLW1Piece1Data v x+matrixValue dLW1Piece2Data v x+matrixValue dLW1Piece3Data v x := by
  unfold dLW1Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def d_LW1_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(4767147854240589807616000000000000000000000000000000000000000), 9⟩ (.add (.add (.add (.matrix dLW1Piece0Data) (.matrix dLW1Piece1Data)) (.matrix dLW1Piece2Data)) (.matrix dLW1Piece3Data)))

set_option maxRecDepth 4096 in
theorem d_LW1_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_D_r6_0_1_V0) d_LW1_coefficient_identity_expression = true := by
  decide +kernel

theorem d_LW1_coefficient_identity :
    realCoefficients numerator_D_r6_0_1_V0 = realMatrixScale (4767147854240589807616000000000000000000000000000000000000000/9 : ℝ) dLW1Combined := by
  have h := CoefficientExpr.check_sound _ _ d_LW1_coefficient_identity_check
  simpa only [d_LW1_coefficient_identity_expression, CoefficientExpr.value, dLW1Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
