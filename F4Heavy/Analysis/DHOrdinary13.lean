module

public import F4Heavy.Analysis.OrdinaryControlSemantics
public import F4Heavy.Finite.Reconstruction.Function13
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part006

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_ordinary_D_r6_endpoint_C_00_coefficients : List Fraction :=
  [⟨350275034936182864870175, 156132458496⟩, ⟨6976982458264580325575, 1858719744⟩, ⟨-54173222535940619375, 9834496⟩, ⟨-3264045761146220375, 526848⟩, ⟨61375394662030625, 50176⟩, ⟨108711478426725, 1792⟩, ⟨129835562175, 256⟩]

theorem dh_ordinary_D_r6_endpoint_C_00 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_C ⟨5, 16⟩ 4) 0).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_C dh_ordinary_D_r6_endpoint_C_00_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 0 v
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [dh_ordinary_D_r6_endpoint_C_00_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_144_D_r6_endpoint_C
  · exact cert_0260_D_r6_endpoint_C_norm_0

def dh_ordinary_D_r6_endpoint_C_01_coefficients : List Fraction :=
  [⟨4168742098000416953230555, 1405192126464⟩, ⟨36329491679697721282415, 5576159232⟩, ⟨-2453793728050016483725, 265531392⟩, ⟨-52115849390548228625, 4741632⟩, ⟨253234444676066975, 150528⟩, ⟨525207377841815, 1792⟩, ⟨1261220884495, 256⟩]

theorem dh_ordinary_D_r6_endpoint_C_01 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_C ⟨5, 16⟩ 4) 1).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_C dh_ordinary_D_r6_endpoint_C_01_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 1 v
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [dh_ordinary_D_r6_endpoint_C_01_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_145_D_r6_endpoint_C
  · exact cert_0261_D_r6_endpoint_C_norm_1

def dh_ordinary_D_r6_endpoint_C_02_coefficients : List Fraction :=
  [⟨346277276263301536521709, 78066229248⟩, ⟨28548527097606107698843, 2788079616⟩, ⟨-1910931668107884444055, 132765696⟩, ⟨-14283413399993463955, 790272⟩, ⟨139796956492302505, 75264⟩, ⟨828926848528283, 896⟩, ⟨4512884905749, 128⟩]

theorem dh_ordinary_D_r6_endpoint_C_02 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_C ⟨5, 16⟩ 4) 2).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_C dh_ordinary_D_r6_endpoint_C_02_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 2 v
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [dh_ordinary_D_r6_endpoint_C_02_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_146_D_r6_endpoint_C
  · exact cert_0262_D_r6_endpoint_C_norm_2

def dh_ordinary_D_r6_endpoint_C_03_coefficients : List Fraction :=
  [⟨838965127808712364636891, 117099343872⟩, ⟨7180227692880905931103, 464679936⟩, ⟨-483578589313304971805, 22127616⟩, ⟨-11279821808440072865, 395136⟩, ⟨23629415544457855, 12544⟩, ⟨1068399702226389, 448⟩, ⟨11759089590237, 64⟩]

theorem dh_ordinary_D_r6_endpoint_C_03 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_C ⟨5, 16⟩ 4) 3).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_C dh_ordinary_D_r6_endpoint_C_03_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 3 v
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [dh_ordinary_D_r6_endpoint_C_03_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_147_D_r6_endpoint_C
  · exact cert_0263_D_r6_endpoint_C_norm_3

def dh_ordinary_D_r6_endpoint_C_04_coefficients : List Fraction :=
  [⟨65520511283988434262941, 5489031744⟩, ⟨501193827206711986633, 21781872⟩, ⟨-34340543760742690955, 1037232⟩, ⟨-823227813522133015, 18522⟩, ⟨1197016992166105, 588⟩, ⟨40258228089313, 7⟩, ⟨777907486169, 1⟩]

theorem dh_ordinary_D_r6_endpoint_C_04 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_C ⟨5, 16⟩ 4) 4).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_C dh_ordinary_D_r6_endpoint_C_04_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 4 v
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [dh_ordinary_D_r6_endpoint_C_04_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_148_D_r6_endpoint_C
  · exact cert_0264_D_r6_endpoint_C_norm_4

theorem dh_ordinary_D_r6_endpoint_C_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_D_r6_endpoint_C v x := by
  apply parent_bernstein_rectangle_positive numerator_D_r6_endpoint_C ⟨5, 16⟩ 4 v x
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num
  · norm_num [numerator_D_r6_endpoint_C]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · exact hx.2
  · intro j hj
    interval_cases j
    · exact dh_ordinary_D_r6_endpoint_C_00 v hv
    · exact dh_ordinary_D_r6_endpoint_C_01 v hv
    · exact dh_ordinary_D_r6_endpoint_C_02 v hv
    · exact dh_ordinary_D_r6_endpoint_C_03 v hv
    · exact dh_ordinary_D_r6_endpoint_C_04 v hv

end F4Heavy.Analysis
