module

public import F4Heavy.Analysis.EFormulaUPieces
public import F4Heavy.Analysis.ESupportData
public import F4Heavy.Analysis.MatrixSemantics

public import F4Heavy.Analysis.EIdentityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

def e_record_E2_U0_piece0Data : List (List Fraction) :=
  [[⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨453383697663, 2199023255552⟩, ⟨5524917301491, 2199023255552⟩, ⟨4723137665259, 2199023255552⟩, ⟨-3670032851721, 2199023255552⟩, ⟨-50684157, 33554432⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨335523392447, 549755813888⟩, ⟨34674004774547, 4398046511104⟩, ⟨52026082339351, 4398046511104⟩, ⟨337015474767, 4398046511104⟩, ⟨-32985796882221, 4398046511104⟩, ⟨-50684157, 16777216⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨355148182781, 1099511627776⟩, ⟨22127078221141, 4398046511104⟩, ⟨75719417475133, 4398046511104⟩, ⟨66990642577445, 4398046511104⟩, ⟨-12043864582875, 4398046511104⟩, ⟨-7666212250377, 1099511627776⟩, ⟨-50684157, 33554432⟩],
   [⟨0, 1⟩, ⟨-378019070593, 549755813888⟩, ⟨-36682425783415, 4398046511104⟩, ⟨-25625594208627, 4398046511104⟩, ⟨18803838500037, 1099511627776⟩, ⟨23383192609009, 1099511627776⟩, ⟨21330977623203, 4398046511104⟩, ⟨-5019117822729, 4398046511104⟩],
   [⟨0, 1⟩, ⟨-2177826807553, 2199023255552⟩, ⟨-60150709192735, 4398046511104⟩, ⟨-134660249707631, 4398046511104⟩, ⟨-4794078279371, 274877906944⟩, ⟨24808232942777, 2199023255552⟩, ⟨65078832749511, 4398046511104⟩, ⟨17622308524023, 4398046511104⟩],
   [⟨0, 1⟩, ⟨-3782831909, 8589934592⟩, ⟨-112565798459, 17179869184⟩, ⟨-350335113419, 17179869184⟩, ⟨-28354482119, 1073741824⟩, ⟨-134618111939, 8589934592⟩, ⟨-61362750333, 17179869184⟩, ⟨-463261581, 17179869184⟩],
   [⟨0, 1⟩, ⟨-7583065, 134217728⟩, ⟨-235075015, 268435456⟩, ⟨-841720215, 268435456⟩, ⟨-83413715, 16777216⟩, ⟨-538397615, 134217728⟩, ⟨-432234705, 268435456⟩, ⟨-68247585, 268435456⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩],
   [⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

noncomputable def e_record_E2_U0_piece0 (lam x : ℝ) : ℝ :=
  matrixValue e_record_E2_U0_piece0Data lam x

def reflectE2U0Piece0 : PolynomialExpr :=
  (.mul (.mul (.mul (.mul (.const ⟨(4), 1⟩) (.add (.mul (.mul reflectE2Delta (.pow reflectEBase 2)) reflectELogDen) (.mul (.add (.mul (.mul (.add reflectE2Gamma (.mul (.const ⟨(-1), 1⟩) reflectE2Delta)) (.pow reflectEBase 2)) reflectELogDen) (.mul (.const ⟨(-1), 1⟩) (.mul (.mul (.mul .activity .parent) reflectE2Upper) (.add (.add reflectE2Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent)))))) reflectE2Height0))) (.mul .activity .parent)) (.add (.mul (.const ⟨(15), 16⟩) reflectE2K) (.mul (.const ⟨(-1), 1⟩) (.mul (.add (.const ⟨(1), 1⟩) .activity) (.add (.add reflectE2Parent reflectEBase) (.mul (.const ⟨(-1), 1⟩) (.mul .activity .parent))))))) (.add (.const ⟨(1), 1⟩) .parent))

set_option maxRecDepth 4096 in
theorem e_record_E2_U0_piece0_coefficients_check :
    PolynomialExpr.check reflectE2U0Piece0 (PolynomialExpr.matrix e_record_E2_U0_piece0Data) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem e_record_E2_U0_piece0_value (lam x : ℝ) :
    eUPiece .E2 lam x (eSupportVertex .E2 lam 0) (eSupportHeight .E2 lam 0) 0 =
      e_record_E2_U0_piece0 lam x := by
  have h := PolynomialExpr.check_sound _ _ e_record_E2_U0_piece0_coefficients_check lam x
  rw [PolynomialExpr.matrix_value] at h
  unfold e_record_E2_U0_piece0
  rw [← h]
  simp only [reflectE2U0Piece0, PolynomialExpr.value, reflectEBase_value, reflectELogDen_value, reflectE2Gamma_value, reflectE2Delta_value, reflectE2K_value, reflectE2Parent_value, reflectE2Upper_value, reflectE2Height0_value, fractionValue, Int.cast_ofNat, Int.cast_neg, Int.cast_one, Nat.cast_one, Nat.cast_ofNat, div_one, eUPiece, sub_eq_add_neg, neg_mul, one_mul]

end F4Heavy.Analysis
