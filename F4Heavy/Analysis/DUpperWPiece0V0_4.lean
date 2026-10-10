module

public import F4Heavy.Analysis.DUpperPrimaryCore
public import F4Heavy.Analysis.MatrixLinear

public import F4Heavy.Analysis.DIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def dUW0V0Piece4Data : List (List Fraction) :=
  [[⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]


def reflectDUW0V0Piece4 : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.mul (.mul (.mul (.const ⟨(-100), 1⟩) reflectDLower) reflectDHeight0) (.pow (.mul reflectDProb (.add (.mul (.const ⟨(2), 1⟩) reflectDParentUpper) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.add reflectDAlpha reflectDBeta) (.const ⟨(12), 1⟩)) (.pow reflectDBase 2))))) 2)) (.add (.const ⟨(1), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.add (.const ⟨(9), 1⟩) (.mul (.const ⟨(-1), 1⟩) .activity))) (.add (.const ⟨(1), 1⟩) .parent)) reflectDSupport)

set_option maxRecDepth 4096 in
theorem dUW0V0_piece4_coefficients_check :
    PolynomialExpr.check reflectDUW0V0Piece4 (PolynomialExpr.matrix dUW0V0Piece4Data) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem dUW0V0_piece4_value (v x : ℝ) :
    dUpperWPiece v x (dLowerNum v x) (1+x) (dVertexNum v 0) (dHeightNum v 0) 4 =
      matrixValue dUW0V0Piece4Data v x := by
  have h := PolynomialExpr.check_sound _ _ dUW0V0_piece4_coefficients_check v x
  rw [PolynomialExpr.matrix_value] at h
  rw [← h]
  simp only [reflectDUW0V0Piece4, PolynomialExpr.value, reflectDBase_value, reflectDProb_value, reflectDAlpha_value, reflectDBeta_value, reflectDLower_value, reflectDSupport_value, reflectDHeight0_value, reflectDParentUpper_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, div_one, dUpperWPiece, sub_eq_add_neg, neg_mul, one_mul]

end F4Heavy.Analysis
