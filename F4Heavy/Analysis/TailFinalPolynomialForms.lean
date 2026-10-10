module

public import F4Heavy.Analysis.TailExtraCoordinates

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def tailFinalAN (r : Row) (lam : ℝ) : ℝ :=
  3*(rowData r).price*(1+2*lam)*tailProbabilityDen r lam-
    8*(1+lam)*tailP1Numerator r lam

def tailFinalAD (r : Row) (lam : ℝ) : ℝ :=
  8*(1+lam)*(tailProbabilityDen r lam)^2*tailTauLo r lam

def tailFinalCN (r : Row) (lam : ℝ) : ℝ :=
  2*tailP1Numerator r lam-(alpha r lam+beta r lam)*(tailProbabilityDen r lam)^2

def tailFinalDN (r : Row) (lam : ℝ) : ℝ :=
  let B := tailProbabilityDen r lam
  let L := tailLNumerator r lam
  (gamma r lam-delta r lam)*B^3*L-lam*tailTauHi r lam*tailP1Numerator r lam*L-
    (tailEta r)^2/2*lam^2*B^4

def tailFinalDD (r : Row) (lam : ℝ) : ℝ :=
  lam*(tailProbabilityDen r lam)^2*tailLNumerator r lam

def tailFinalGN (r : Row) (lam jn jd : ℝ) : ℝ :=
  delta r lam*(tailProbabilityDen r lam)^3*tailLNumerator r lam*jd+tailFinalDN r lam*jn

def tailFinalTN (r : Row) (lam hn hd jn jd : ℝ) : ℝ :=
  let B := tailProbabilityDen r lam
  let L := tailLNumerator r lam
  let C := tailFinalCN r lam
  let D := tailFinalDN r lam
  4*tailFinalGN r lam jn jd*(tailFinalAN r lam*hd+beta r lam*hn*tailFinalAD r lam)*lam*hd+
    32*delta r lam*B*(1+lam)*B^2*jd*tailTauLo r lam*(C*lam*L*hn*hd+D*hn^2)-
    8*jn*C^2*lam^2*(1+lam)*L*tailTauLo r lam*hd^2

def tailFinalTD (r : Row) (lam hd jd : ℝ) : ℝ :=
  8*lam^2*(1+lam)*(tailProbabilityDen r lam)^4*tailLNumerator r lam*jd*tailTauLo r lam*hd^2

theorem tail_LNumerator_positive (r : Row) (lam : ℝ) (hl : 0 < lam)
    (hL : 0 < tailLStar r lam) : 0 < tailLNumerator r lam := by
  have hs := tail_scale_positive r
  have hB : 0 < tailProbabilityDen r lam := by unfold tailProbabilityDen; positivity
  have hd : lam*(tailProbabilityDen r lam)^2 ≠ 0 := by positivity
  have heq := tail_middle_quotient r lam hl 8 (by omega) (by omega)
  change tailLStar r lam = tailLNumerator r lam/(lam*(tailProbabilityDen r lam)^2) at heq
  rw [← (eq_div_iff hd).mp heq]
  positivity

theorem tail_final_A_quotient (r : Row) (lam : ℝ) (hl : 0 < lam)
    (hT : tailTauLo r lam ≠ 0) : tailA r lam = tailFinalAN r lam/tailFinalAD r lam := by
  have hs := tail_scale_positive r
  have hB : tailScale r*(1+lam)+lam ≠ 0 := by positivity
  have h1 : 1+lam ≠ 0 := by positivity
  simp only [tailA,tailFinalAN,tailFinalAD,tailP1Numerator,tailProbabilityDen,tailP1,tailV,
    tailK,tailS_rational r lam hl,tailPStar]
  field_simp [ne_of_gt hl,hT,hB,h1]
  <;> ring

theorem tail_final_C_quotient (r : Row) (lam : ℝ) (hl : 0 < lam) :
    tailC r lam = tailFinalCN r lam/(tailProbabilityDen r lam)^2 := by
  have hs := tail_scale_positive r
  have hB : tailScale r*(1+lam)+lam ≠ 0 := by positivity
  simp only [tailC,tailFinalCN,tailP1Numerator,tailProbabilityDen,tailP1,tailV,tailPStar]
  field_simp [hB]
  <;> ring

theorem tail_final_D_quotient (r : Row) (lam : ℝ) (hl : 0 < lam)
    (hL : 0 < tailLStar r lam) : tailD r lam = tailFinalDN r lam/tailFinalDD r lam := by
  have hs := tail_scale_positive r
  have hB : tailScale r*(1+lam)+lam ≠ 0 := by positivity
  have hN := ne_of_gt (tail_LNumerator_positive r lam hl hL)
  have heq := tail_middle_quotient r lam hl 8 (by omega) (by omega)
  change tailLStar r lam = tailLNumerator r lam/(lam*(tailProbabilityDen r lam)^2) at heq
  unfold tailD
  rw [heq]
  simp only [tailFinalDN,tailFinalDD,tailP1Numerator,tailProbabilityDen,tailP1,tailV,tailPStar] at *
  field_simp [ne_of_gt hl,hB,hN]
  <;> ring

theorem tail_final_reserve_quotient (r : Row) (lam : ℝ) (hl : 0 < lam) :
    tailReserveK r lam = delta r lam*tailProbabilityDen r lam/lam := by
  simp only [tailReserveK,tailPStar,tailProbabilityDen,div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring


theorem tail_final_G_quotient (r : Row) (lam jn jd : ℝ) (hl : 0 < lam)
    (hL : 0 < tailLStar r lam) (hjd : jd ≠ 0) :
    tailReserveK r lam+tailD r lam*(jn/jd) =
      tailFinalGN r lam jn jd/(tailFinalDD r lam*jd) := by
  have hs := tail_scale_positive r
  have hB : tailProbabilityDen r lam ≠ 0 := by unfold tailProbabilityDen; positivity
  have hN := ne_of_gt (tail_LNumerator_positive r lam hl hL)
  rw [tail_final_reserve_quotient r lam hl,tail_final_D_quotient r lam hl hL]
  unfold tailFinalGN tailFinalDD
  field_simp [ne_of_gt hl,hB,hN,hjd]
  <;> ring

theorem tail_final_T_quotient (r : Row) (lam hn hd jn jd : ℝ) (hl : 0 < lam)
    (hT : tailTauLo r lam ≠ 0) (hL : 0 < tailLStar r lam)
    (hhd : hd ≠ 0) (hjd : jd ≠ 0) :
    tailT r lam (hn/hd) (jn/jd) = tailFinalTN r lam hn hd jn jd/tailFinalTD r lam hd jd := by
  have hs := tail_scale_positive r
  have hB : tailProbabilityDen r lam ≠ 0 := by unfold tailProbabilityDen; positivity
  have hN := ne_of_gt (tail_LNumerator_positive r lam hl hL)
  have h1 : 1+lam ≠ 0 := by positivity
  unfold tailT
  rw [tail_final_A_quotient r lam hl hT,tail_final_C_quotient r lam hl,
    tail_final_D_quotient r lam hl hL,tail_final_reserve_quotient r lam hl]
  unfold responseNumerator tailFinalTN tailFinalTD tailFinalGN tailFinalAD tailFinalDD
  field_simp [ne_of_gt hl,hB,hN,h1,hT,hhd,hjd]
  <;> ring

theorem tail_child_hb_quotient (lam : ℝ) (hl : 0 < lam) :
    tailChildHb lam = (33*(29+10*lam)-8*(10*lam))/(32*(29+10*lam)) := by
  have hd : 29+10*lam ≠ 0 := by positivity
  unfold tailChildHb tailChildC
  field_simp [hd]
  <;> ring

end
end F4Heavy.Analysis
