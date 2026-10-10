module

public import F4Heavy.Analysis.HLowerWPiece0_0
public import F4Heavy.Analysis.HLowerWPiece0_1
public import F4Heavy.Analysis.HLowerWPiece0_2
public import F4Heavy.Analysis.HLowerWPiece0_3
public import F4Heavy.Finite.Reconstruction.Function27

public import F4Heavy.Analysis.MatrixCoefficientIdentity

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

noncomputable def hLW0Combined : List (List ℝ) := (realMatrixAdd (realMatrixAdd (realMatrixAdd (realCoefficients hLW0Piece0Data) (realCoefficients hLW0Piece1Data)) (realCoefficients hLW0Piece2Data)) (realCoefficients hLW0Piece3Data))

theorem h_LW0_combined_value (v x : ℝ) :
    realMatrixValue hLW0Combined v x = matrixValue hLW0Piece0Data v x+
      matrixValue hLW0Piece1Data v x+matrixValue hLW0Piece2Data v x+matrixValue hLW0Piece3Data v x := by
  unfold hLW0Combined
  rw [realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl), realMatrixValue_add _ _ v x (by rfl)]
  simp only [realMatrixValue_coefficients]

def h_LW0_coefficient_identity_expression : CoefficientExpr :=
  (.scale ⟨(562949953421312000000000000000000000000000000000000000000), 1⟩ (.add (.add (.add (.matrix hLW0Piece0Data) (.matrix hLW0Piece1Data)) (.matrix hLW0Piece2Data)) (.matrix hLW0Piece3Data)))

set_option maxRecDepth 4096 in
theorem h_LW0_coefficient_identity_check :
    CoefficientExpr.check (.matrix numerator_H_r6_0_0_V0) h_LW0_coefficient_identity_expression = true := by
  decide +kernel

theorem h_LW0_coefficient_identity :
    realCoefficients numerator_H_r6_0_0_V0 = realMatrixScale (562949953421312000000000000000000000000000000000000000000/1 : ℝ) hLW0Combined := by
  have h := CoefficientExpr.check_sound _ _ h_LW0_coefficient_identity_check
  simpa only [h_LW0_coefficient_identity_expression, CoefficientExpr.value, hLW0Combined, fractionValue,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one] using h

end F4Heavy.Analysis
