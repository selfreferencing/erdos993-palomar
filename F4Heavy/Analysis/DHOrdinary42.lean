module

public import F4Heavy.Analysis.OrdinaryControlSemantics
public import F4Heavy.Finite.Reconstruction.Function42
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part027

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_ordinary_H_r6_endpoint_C_00_coefficients : List Fraction :=
  [⟨1228008886625557803985, 240945152⟩, ⟨-35984515932630333993, 2151296⟩, ⟨-36949461594794576351, 1229312⟩, ⟨-216020901545756161, 10976⟩, ⟨-43089491520643357, 6272⟩, ⟨-36699540345451, 28⟩, ⟨-3426503598293, 32⟩]

theorem dh_ordinary_H_r6_endpoint_C_00 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_C ⟨1, 4⟩ 4) 0).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_C dh_ordinary_H_r6_endpoint_C_00_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 0 v
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [dh_ordinary_H_r6_endpoint_C_00_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_336_H_r6_endpoint_C
  · exact cert_1111_H_r6_endpoint_C_norm_0

def dh_ordinary_H_r6_endpoint_C_01_coefficients : List Fraction :=
  [⟨12022031738223453169595, 1927561216⟩, ⟨-954763977461043209583, 68841472⟩, ⟨-277049619713614973791, 9834496⟩, ⟨-3635925909411764509, 175616⟩, ⟨-436419014378059187, 50176⟩, ⟨-3684436252186855, 1792⟩, ⟨-51920767452553, 256⟩]

theorem dh_ordinary_H_r6_endpoint_C_01 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_C ⟨1, 4⟩ 4) 1).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_C dh_ordinary_H_r6_endpoint_C_01_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 1 v
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [dh_ordinary_H_r6_endpoint_C_01_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_337_H_r6_endpoint_C
  · exact cert_1112_H_r6_endpoint_C_norm_1

def dh_ordinary_H_r6_endpoint_C_02_coefficients : List Fraction :=
  [⟨1935973116703859133895, 240945152⟩, ⟨-58572575776440812475, 8605184⟩, ⟨-23543552569456406171, 1229312⟩, ⟨-386606070429954209, 21952⟩, ⟨-65418240867345631, 6272⟩, ⟨-747229406212307, 224⟩, ⟨-12952674553517, 32⟩]

theorem dh_ordinary_H_r6_endpoint_C_02 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_C ⟨1, 4⟩ 4) 2).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_C dh_ordinary_H_r6_endpoint_C_02_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 2 v
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [dh_ordinary_H_r6_endpoint_C_02_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_338_H_r6_endpoint_C
  · exact cert_1113_H_r6_endpoint_C_norm_2

def dh_ordinary_H_r6_endpoint_C_03_coefficients : List Fraction :=
  [⟨1326765374908616918825, 120472576⟩, ⟨30429656661561661803, 4302592⟩, ⟨846580083755256491, 614656⟩, ⟨-84814669385036431, 10976⟩, ⟨-38112401771743505, 3136⟩, ⟨-645637571228029, 112⟩, ⟨-13625316150883, 16⟩]

theorem dh_ordinary_H_r6_endpoint_C_03 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_C ⟨1, 4⟩ 4) 3).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_C dh_ordinary_H_r6_endpoint_C_03_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 3 v
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [dh_ordinary_H_r6_endpoint_C_03_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_339_H_r6_endpoint_C
  · exact cert_1114_H_r6_endpoint_C_norm_3

def dh_ordinary_H_r6_endpoint_C_04_coefficients : List Fraction :=
  [⟨120641107082017046765, 7529536⟩, ⟨8466641826424965231, 268912⟩, ⟨1490638025675347271, 38416⟩, ⟨7629991238706413, 686⟩, ⟨-3019078684619093, 196⟩, ⟨-76015031731129, 7⟩, ⟨-1870644019711, 1⟩]

theorem dh_ordinary_H_r6_endpoint_C_04 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_C ⟨1, 4⟩ 4) 4).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_C dh_ordinary_H_r6_endpoint_C_04_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 4 v
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [dh_ordinary_H_r6_endpoint_C_04_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_340_H_r6_endpoint_C
  · exact cert_1115_H_r6_endpoint_C_norm_4

theorem dh_ordinary_H_r6_endpoint_C_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_H_r6_endpoint_C v x := by
  apply parent_bernstein_rectangle_positive numerator_H_r6_endpoint_C ⟨1, 4⟩ 4 v x
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num
  · norm_num [numerator_H_r6_endpoint_C]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · exact hx.2
  · intro j hj
    interval_cases j
    · exact dh_ordinary_H_r6_endpoint_C_00 v hv
    · exact dh_ordinary_H_r6_endpoint_C_01 v hv
    · exact dh_ordinary_H_r6_endpoint_C_02 v hv
    · exact dh_ordinary_H_r6_endpoint_C_03 v hv
    · exact dh_ordinary_H_r6_endpoint_C_04 v hv

end F4Heavy.Analysis
