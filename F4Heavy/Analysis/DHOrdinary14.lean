module

public import F4Heavy.Analysis.OrdinaryControlSemantics
public import F4Heavy.Finite.Reconstruction.Function14
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part006

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_ordinary_D_r6_endpoint_D_00_coefficients : List Fraction :=
  [⟨12098159339768171010370281491312525, 2141245145088⟩, ⟨-453469851550379426330631428462905, 50982027264⟩, ⟨1346308971393878672811766266745, 606928896⟩, ⟨158144034428831573823856022015, 14450688⟩, ⟨-534966575956465568963626415, 688128⟩, ⟨-379094719388162733632405, 16384⟩]

theorem dh_ordinary_D_r6_endpoint_D_00 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_D ⟨5, 16⟩ 4) 0).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_D dh_ordinary_D_r6_endpoint_D_00_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 0 v
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [dh_ordinary_D_r6_endpoint_D_00_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_149_D_r6_endpoint_D
  · exact cert_0267_D_r6_endpoint_D_norm_0

def dh_ordinary_D_r6_endpoint_D_01_coefficients : List Fraction :=
  [⟨12386417735864645149854750011162785, 1070622572544⟩, ⟨-316429811787164549533802620233617, 25491013632⟩, ⟨121822329902253253993870554293, 303464448⟩, ⟨121990032406734753329984165071, 7225344⟩, ⟨-78979695874796145879997531, 344064⟩, ⟨-784550921927277308432317, 8192⟩]

theorem dh_ordinary_D_r6_endpoint_D_01 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_D ⟨5, 16⟩ 4) 1).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_D dh_ordinary_D_r6_endpoint_D_01_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 1 v
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [dh_ordinary_D_r6_endpoint_D_01_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_150_D_r6_endpoint_D
  · exact cert_0268_D_r6_endpoint_D_norm_1

def dh_ordinary_D_r6_endpoint_D_02_coefficients : List Fraction :=
  [⟨971566651360868720697492594694645, 66913910784⟩, ⟨-16519047063105954768962782983449, 1593188352⟩, ⟨31746018509078008028814735641, 18966528⟩, ⟨9356154504082543044799014967, 451584⟩, ⟨38916968289719534724575273, 21504⟩, ⟨-97227877839618238760869, 512⟩]

theorem dh_ordinary_D_r6_endpoint_D_02 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_D ⟨5, 16⟩ 4) 2).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_D dh_ordinary_D_r6_endpoint_D_02_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 2 v
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [dh_ordinary_D_r6_endpoint_D_02_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_151_D_r6_endpoint_D
  · exact cert_0269_D_r6_endpoint_D_norm_2

def dh_ordinary_D_r6_endpoint_D_03_coefficients : List Fraction :=
  [⟨103197316886374544433219631429015, 8364238848⟩, ⟨-483229149166548071278198766843, 199148544⟩, ⟨24553125943810149827742185027, 2370816⟩, ⟨1330012112648107617103491829, 56448⟩, ⟨12976321120257262048788371, 2688⟩, ⟨-949083401970603211423, 64⟩]

theorem dh_ordinary_D_r6_endpoint_D_03 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_D ⟨5, 16⟩ 4) 3).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_D dh_ordinary_D_r6_endpoint_D_03_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 3 v
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [dh_ordinary_D_r6_endpoint_D_03_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_152_D_r6_endpoint_D
  · exact cert_0270_D_r6_endpoint_D_norm_3

def dh_ordinary_D_r6_endpoint_D_04_coefficients : List Fraction :=
  [⟨162695888855706120117006778325, 65345616⟩, ⟨17024798453282746926046711535, 1555848⟩, ⟨571906589011392053498646745, 18522⟩, ⟨12354683514833213925942335, 441⟩, ⟨201692061639360275047945, 21⟩, ⟨1064765589908872569350, 1⟩]

theorem dh_ordinary_D_r6_endpoint_D_04 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_D_r6_endpoint_D ⟨5, 16⟩ 4) 4).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_D_r6_endpoint_D dh_ordinary_D_r6_endpoint_D_04_coefficients ⟨5, 16⟩ ⟨0, 1⟩ ⟨5, 21⟩ ⟨5, 42⟩ 4 4 v
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [dh_ordinary_D_r6_endpoint_D_04_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_153_D_r6_endpoint_D
  · exact cert_0271_D_r6_endpoint_D_norm_4

theorem dh_ordinary_D_r6_endpoint_D_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_D_r6_endpoint_D v x := by
  apply parent_bernstein_rectangle_positive numerator_D_r6_endpoint_D ⟨5, 16⟩ 4 v x
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num
  · norm_num [numerator_D_r6_endpoint_D]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Nat.cast_ofNat] using hx.1
  · exact hx.2
  · intro j hj
    interval_cases j
    · exact dh_ordinary_D_r6_endpoint_D_00 v hv
    · exact dh_ordinary_D_r6_endpoint_D_01 v hv
    · exact dh_ordinary_D_r6_endpoint_D_02 v hv
    · exact dh_ordinary_D_r6_endpoint_D_03 v hv
    · exact dh_ordinary_D_r6_endpoint_D_04 v hv

end F4Heavy.Analysis
