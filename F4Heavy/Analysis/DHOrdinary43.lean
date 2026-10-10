module

public import F4Heavy.Analysis.OrdinaryControlSemantics
public import F4Heavy.Finite.Reconstruction.Function43
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part027
public import F4Heavy.Finite.Certificates.Part028

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_ordinary_H_r6_endpoint_D_00_coefficients : List Fraction :=
  [⟨463651997092787495589121958325, 17210368⟩, ⟨-652865584757015612126810583705, 4917248⟩, ⟨-529096016176046768218317585, 10976⟩, ⟨1612255721107128971822844535, 12544⟩, ⟨35552031925454105280654385, 448⟩, ⟨1540125009824301290686515, 128⟩]

theorem dh_ordinary_H_r6_endpoint_D_00 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_D ⟨1, 4⟩ 4) 0).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_D dh_ordinary_H_r6_endpoint_D_00_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 0 v
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [dh_ordinary_H_r6_endpoint_D_00_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_341_H_r6_endpoint_D
  · exact cert_1118_H_r6_endpoint_D_norm_0

def dh_ordinary_H_r6_endpoint_D_01_coefficients : List Fraction :=
  [⟨1289480028736954126751837746755, 17210368⟩, ⟨-892891394533347375576037649727, 4917248⟩, ⟨-667087477271438946525046137, 5488⟩, ⟨2336822909932155432594283009, 12544⟩, ⟨61651343637563210740468639, 448⟩, ⟨2927639426167209554726901, 128⟩]

theorem dh_ordinary_H_r6_endpoint_D_01 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_D ⟨1, 4⟩ 4) 1).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_D dh_ordinary_H_r6_endpoint_D_01_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 1 v
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [dh_ordinary_H_r6_endpoint_D_01_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_342_H_r6_endpoint_D
  · exact cert_1119_H_r6_endpoint_D_norm_1

def dh_ordinary_H_r6_endpoint_D_02_coefficients : List Fraction :=
  [⟨254697256236310699529890756515, 2151296⟩, ⟨-141709163748384955234903702431, 614656⟩, ⟨-268888043398565979867597087, 1372⟩, ⟨404818927206091691477638481, 1568⟩, ⟨12333706912964203318844423, 56⟩, ⟨643156676497528212264501, 16⟩]

theorem dh_ordinary_H_r6_endpoint_D_02 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_D ⟨1, 4⟩ 4) 2).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_D dh_ordinary_H_r6_endpoint_D_02_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 2 v
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [dh_ordinary_H_r6_endpoint_D_02_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_343_H_r6_endpoint_D
  · exact cert_1120_H_r6_endpoint_D_norm_2

def dh_ordinary_H_r6_endpoint_D_03_coefficients : List Fraction :=
  [⟨153245272773877772899408352745, 1075648⟩, ⟨-89183392994504378269917204573, 307328⟩, ⟨-85824137390003166686155788, 343⟩, ⟨286864326591939975599299651, 784⟩, ⟨9363688344261410159798221, 28⟩, ⟨532213774573284882211839, 8⟩]

theorem dh_ordinary_H_r6_endpoint_D_03 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_D ⟨1, 4⟩ 4) 3).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_D dh_ordinary_H_r6_endpoint_D_03_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 3 v
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [dh_ordinary_H_r6_endpoint_D_03_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_344_H_r6_endpoint_D
  · exact cert_1121_H_r6_endpoint_D_norm_3

def dh_ordinary_H_r6_endpoint_D_04_coefficients : List Fraction :=
  [⟨4259619487251678986225935815, 33614⟩, ⟨-3687775882382115007216581651, 9604⟩, ⟨-90847812118791148810360032, 343⟩, ⟨26876914484233361937822682, 49⟩, ⟨3524437327409622652316824, 7⟩, ⟨108762116571217018917444, 1⟩]

theorem dh_ordinary_H_r6_endpoint_D_04 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_D ⟨1, 4⟩ 4) 4).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_D dh_ordinary_H_r6_endpoint_D_04_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 4 4 v
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [dh_ordinary_H_r6_endpoint_D_04_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_345_H_r6_endpoint_D
  · exact cert_1122_H_r6_endpoint_D_norm_4

theorem dh_ordinary_H_r6_endpoint_D_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_H_r6_endpoint_D v x := by
  apply parent_bernstein_rectangle_positive numerator_H_r6_endpoint_D ⟨1, 4⟩ 4 v x
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num
  · norm_num [numerator_H_r6_endpoint_D]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · exact hx.2
  · intro j hj
    interval_cases j
    · exact dh_ordinary_H_r6_endpoint_D_00 v hv
    · exact dh_ordinary_H_r6_endpoint_D_01 v hv
    · exact dh_ordinary_H_r6_endpoint_D_02 v hv
    · exact dh_ordinary_H_r6_endpoint_D_03 v hv
    · exact dh_ordinary_H_r6_endpoint_D_04 v hv

end F4Heavy.Analysis
