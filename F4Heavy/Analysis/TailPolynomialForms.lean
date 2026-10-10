module

public import F4Heavy.Analysis.TailRationalForms
public import Mathlib.Tactic.IntervalCases

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def tailProbabilityDen (r : Row) (lam : ℝ) : ℝ := tailScale r*(1+lam)+lam
def tailP1Numerator (r : Row) (lam : ℝ) : ℝ :=
  let B := tailProbabilityDen r lam
  B^2-lam*B+gamma r lam*(B^2-lam*B/2-lam^2/12)
def tailANumerator (r : Row) (lam : ℝ) : ℝ :=
  (1+gamma r lam/2)*tailProbabilityDen r lam+gamma r lam*lam/6
def tailLNumerator (r : Row) (lam : ℝ) : ℝ :=
  (gamma r lam-delta r lam)*tailScale r*(1+lam)*(tailProbabilityDen r lam)^2-
    2*lam^2*tailANumerator r lam
def tailMiddleNumerator (r : Row) (lam : ℝ) : Nat → ℝ :=
  let B := tailProbabilityDen r lam
  let A := tailANumerator r lam
  let P := tailP1Numerator r lam
  let H := tailTauHi r lam
  let g := gamma r lam
  let d := delta r lam
  let a := alpha r lam
  let b := beta r lam
  let price := (rowData r).price
  let dn := (g-d)*B-g*lam*H
  let mn := 8*(a-g)*(1+lam)*B-price*(1+2*lam)
  let cn := (a+b-2*g)*B+2*g*lam
  fun i => match i with
  | 5 => dn*mn*B-2*(1+lam)*lam*H*cn^2
  | 6 => 8*(1+lam)*P-3*price*(1+2*lam)*B
  | 7 => 8*(1+lam)*P-3*price*(1+2*lam)*B-
      8*(1+lam)*lam*H*A-3*price*(1+2*lam)*H*B
  | 8 => tailLNumerator r lam
  | 9 => (g-d)*tailScale r*(1+lam)*B^3-lam*B*P-
      lam^2*H*(B-lam)*A+tailEta r*lam*B^3
  | 10 => 2*(2+2*g-a-b)*B^2-4*(2+g)*lam*B-g*lam^2
  | 11 => 2*d*B^3*(6+lam)-2*lam^2*(2*P-(a+b)*B^2)
  | 12 => 2*P-(a+b)*B^2
  | _ => 0
def tailMiddleDenominator (r : Row) (lam : ℝ) : Nat → ℝ :=
  let B := tailProbabilityDen r lam
  fun i => match i with
  | 5 => 2*(1+lam)*B^3
  | 6 | 7 => 8*(1+lam)*B^2
  | 8 => lam*B^2
  | 9 => lam*B^3
  | 10 => 2*B^2
  | 11 => B^3*(6+lam)
  | 12 => B^2
  | _ => 1

theorem tailS_rational (r : Row) (lam : ℝ) (hl : 0 < lam) :
    tailS r lam = (rowData r).price*(1+2*lam)/(2*lam*(1+lam)) := by
  have h1 : 1+lam ≠ 0 := by positivity
  unfold tailS q
  field_simp [ne_of_gt hl,h1]
  <;> ring

theorem tail_middle_quotient (r : Row) (lam : ℝ) (hl : 0 < lam)
    (i : Nat) (hlo : 5 ≤ i) (hhi : i ≤ 12) :
    tailGuard r lam i = tailMiddleNumerator r lam i/tailMiddleDenominator r lam i := by
  have hs := tail_scale_positive r
  have h1 : 1+lam ≠ 0 := by positivity
  have h6 : 6+lam ≠ 0 := by positivity
  have hB : tailScale r*(1+lam)+lam ≠ 0 := by positivity
  interval_cases i <;>
    simp only [tailMiddleNumerator, tailMiddleDenominator, tailProbabilityDen,
      tailP1Numerator, tailANumerator, tailLNumerator,
      tailGuard, tailD0, tailM0, tailC0, tailPStar, tailP1, tailV,
      tailK, tailLStar, tailEStar, tailAStar, tailChildB, tailC,
      tailS_rational r lam hl] <;>
    field_simp [ne_of_gt hl,h1,h6,hB] <;> ring

end
end F4Heavy.Analysis
