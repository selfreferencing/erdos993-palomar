module

public import F4Heavy.Analysis.OrdinaryControlSemantics
public import F4Heavy.Finite.Reconstruction.Function41
public import Mathlib.Tactic.IntervalCases
public import F4Heavy.Finite.Certificates.Part027

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def dh_ordinary_H_r6_endpoint_R_00_coefficients : List Fraction :=
  [⟨70040159066014929348313185885434272365, 53971714048⟩, ⟨4397108201997404492202312740734894353, 550731776⟩, ⟨56331755749910602030227618257774931, 39337984⟩, ⟨-24484440141119436039403642886239583, 2809856⟩, ⟨-1352708696507842228860332944949559, 200704⟩, ⟨-25600943921806993895740347693221, 14336⟩, ⟨-146644206727440987677589759239, 1024⟩, ⟨2084884755733501263929166501, 512⟩]

theorem dh_ordinary_H_r6_endpoint_R_00 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 0).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_00_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 0 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_00_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_329_H_r6_endpoint_R
  · exact cert_1102_H_r6_endpoint_R_norm_0

def dh_ordinary_H_r6_endpoint_R_01_coefficients : List Fraction :=
  [⟨314525693559210671909030963577833259525, 215886856192⟩, ⟨24901868237008142225815788903295426515, 2202927104⟩, ⟨331900391104066568212180059264668079, 157351936⟩, ⟨-149949079758055097949716986376382689, 11239424⟩, ⟨-8592616596062149370522958377034727, 802816⟩, ⟨-169901527364110862474903740396359, 57344⟩, ⟨-1073632264849764941377232528283, 4096⟩, ⟨7276076567658162068806294803, 2048⟩]

theorem dh_ordinary_H_r6_endpoint_R_01 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 1).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_01_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 1 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_01_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_330_H_r6_endpoint_R
  · exact cert_1103_H_r6_endpoint_R_norm_1

def dh_ordinary_H_r6_endpoint_R_02_coefficients : List Fraction :=
  [⟨42619997388262277411464094442587888115, 26985857024⟩, ⟨3917277274656674297305385351373833205, 275365888⟩, ⟨187319537249599964798066539491078429, 98344960⟩, ⟨-133373319081549777083419119869647379, 7024640⟩, ⟨-1575327945158112130020372259212865, 100352⟩, ⟨-169844758509658916820193404249829, 35840⟩, ⟨-1409120209512771796288965435937, 2560⟩, ⟨-20988875124010949932677217143, 1280⟩]

theorem dh_ordinary_H_r6_endpoint_R_02 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 2).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_02_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 2 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_02_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_331_H_r6_endpoint_R
  · exact cert_1104_H_r6_endpoint_R_norm_2

def dh_ordinary_H_r6_endpoint_R_03_coefficients : List Fraction :=
  [⟨55857013085097292729158839188218278661, 26985857024⟩, ⟨21051538233232070815373533115250967551, 1376829440⟩, ⟨-138630398675283201426377819641671381, 98344960⟩, ⟨-176850149337115352289426363717622853, 7024640⟩, ⟨-10424602088445663798670698413643267, 501760⟩, ⟨-261977273972934733560252805871939, 35840⟩, ⟨-3331338920989202276193813415751, 2560⟩, ⟨-28332226033596333389188699725, 256⟩]

theorem dh_ordinary_H_r6_endpoint_R_03 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 3).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_03_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 3 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_03_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_332_H_r6_endpoint_R
  · exact cert_1105_H_r6_endpoint_R_norm_3

def dh_ordinary_H_r6_endpoint_R_04_coefficients : List Fraction :=
  [⟨6382104195364356279036763696675935039, 1686616064⟩, ⟨1037956213392033175873397723381725629, 86051840⟩, ⟨-76090824569838182098491165871321167, 6146560⟩, ⟨-13605112919421864022472763618790319, 439040⟩, ⟨-727942969397025719218184736784921, 31360⟩, ⟨-24106539954508163311365073867593, 2240⟩, ⟨-516548540070815034066025999749, 160⟩, ⟨-6963275455828443313475898375, 16⟩]

theorem dh_ordinary_H_r6_endpoint_R_04 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 4).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_04_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 4 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_04_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_333_H_r6_endpoint_R
  · exact cert_1106_H_r6_endpoint_R_norm_4

def dh_ordinary_H_r6_endpoint_R_05_coefficients : List Fraction :=
  [⟨1740534352116070316257039836630117135, 210827008⟩, ⟨1535276598149894192680783799635617, 2151296⟩, ⟨-6034781693047632443514817747798563, 153664⟩, ⟨-383515905422771670837029531723915, 10976⟩, ⟨-13337042672705830975826761901141, 784⟩, ⟨-826259484619092674875486263037, 56⟩, ⟨-31622676875826553584505246465, 4⟩, ⟨-2770485188810451064635787887, 2⟩]

theorem dh_ordinary_H_r6_endpoint_R_05 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 5).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_05_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 5 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_05_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_334_H_r6_endpoint_R
  · exact cert_1107_H_r6_endpoint_R_norm_5

def dh_ordinary_H_r6_endpoint_R_06_coefficients : List Fraction :=
  [⟨946133607019183489027542770860525635, 52706752⟩, ⟨-13193799139291251845151067949477643, 537824⟩, ⟨-3681710261802299063925260871360567, 38416⟩, ⟨-95412053272795399918441836114071, 2744⟩, ⟨1800082826586089386653485291535, 196⟩, ⟨-252402226279358381435823159713, 14⟩, ⟨-18461083290634047426940788605, 1⟩, ⟨-3858678323721128126417273814, 1⟩]

theorem dh_ordinary_H_r6_endpoint_R_06 (v : ℝ) (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) :
    0 < realHorner ((column (parentColumns numerator_H_r6_endpoint_R ⟨1, 4⟩ 6) 6).map fractionValue) v := by
  apply ordinaryControl_norm_positive numerator_H_r6_endpoint_R dh_ordinary_H_r6_endpoint_R_06_coefficients ⟨1, 4⟩ ⟨0, 1⟩ ⟨1, 7⟩ ⟨1, 14⟩ 6 6 v
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [dh_ordinary_H_r6_endpoint_R_06_coefficients]
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · rw [abs_le]
    norm_num [fractionValue]
    constructor <;> linarith only [hv.1, hv.2]
  · exact reconstruct_335_H_r6_endpoint_R
  · exact cert_1108_H_r6_endpoint_R_norm_6

theorem dh_ordinary_H_r6_endpoint_R_rectangle_positive (v x : ℝ)
    (hv : (0/1 : ℝ) ≤ v ∧ v ≤ (1/7 : ℝ)) (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < matrixValue numerator_H_r6_endpoint_R v x := by
  apply parent_bernstein_rectangle_positive numerator_H_r6_endpoint_R ⟨1, 4⟩ 6 v x
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num
  · norm_num [numerator_H_r6_endpoint_R]
  · norm_num [fractionValue]
  · simpa only [fractionValue, Int.cast_ofNat, Int.cast_one, Nat.cast_ofNat, Nat.cast_one] using hx.1
  · exact hx.2
  · intro j hj
    interval_cases j
    · exact dh_ordinary_H_r6_endpoint_R_00 v hv
    · exact dh_ordinary_H_r6_endpoint_R_01 v hv
    · exact dh_ordinary_H_r6_endpoint_R_02 v hv
    · exact dh_ordinary_H_r6_endpoint_R_03 v hv
    · exact dh_ordinary_H_r6_endpoint_R_04 v hv
    · exact dh_ordinary_H_r6_endpoint_R_05 v hv
    · exact dh_ordinary_H_r6_endpoint_R_06 v hv

end F4Heavy.Analysis
