module

public import F4Heavy.Analysis.EFormulaUPieces
public import F4Heavy.Analysis.ESupportData
public import F4Heavy.Analysis.MatrixSemantics

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def e_record_E2_U0_piece4Data : List (List Fraction) :=
  [[⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

noncomputable def e_record_E2_U0_piece4 (lam x : ℝ) : ℝ :=
  matrixValue e_record_E2_U0_piece4Data lam x

def reflectE2U0Piece4 : PolynomialExpr :=
  (.mul (.mul (.mul (.mul reflectE2Lower reflectE2Height0) (.pow (.mul (.mul .activity .parent) (.add (.mul (.const ⟨(2), 1⟩) (.add (.add reflectE2Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))) (.mul (.const ⟨(-1), 1⟩) (.mul (.add reflectE2Alpha reflectE2Beta) reflectEBase)))) 2)) (.add (.const ⟨(1), 1⟩) .activity)) reflectELogDen)

set_option maxRecDepth 4096 in
theorem e_record_E2_U0_piece4_coefficients_check :
    PolynomialExpr.check reflectE2U0Piece4 (PolynomialExpr.matrix e_record_E2_U0_piece4Data) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E2_U0_piece4_value (lam x : ℝ) :
    eUPiece .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0) 4 =
      e_record_E2_U0_piece4 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E2_U0_piece4_coefficients_check lam x
  rw [PolynomialExpr.matrix_value] at h
  unfold e_record_E2_U0_piece4
  rw [← h]
  simp only [reflectE2U0Piece4, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, reflectE2Alpha_value, reflectE2Beta_value, reflectE2Parent_value, reflectE2Lower_value, reflectE2Height0_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, eUPiece, sub_eq_add_neg, neg_mul, one_mul]

end F4Heavy.Analysis
