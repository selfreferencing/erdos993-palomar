module

public import F4Heavy.Analysis.EFormulaClearing
public import F4Heavy.Analysis.ResponseChord

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eUFormula (r : Row) (lam x h L : ℝ) : ℝ :=
  let P := eParentBaseX r lam x + 1 - eProbabilityX lam x
  let N := (15/16)*eHeavyKX r lam x - P
  let d := gamma r lam-delta r lam-eProbabilityX lam x*parentLogUpper r lam x*P
  let c := eProbabilityX lam x*(2*P-alpha r lam-beta r lam)
  let b := eProbabilityX lam x*beta r lam
  4*(delta r lam+d*L)*(eProbabilityX lam x*N+parentLogLower r lam x*b*h) +
    4*delta r lam*parentLogLower r lam x*(c*h+d*h^2)-parentLogLower r lam x*L*c^2

noncomputable def eUNumerator (r : Row) (lam x h L : ℝ) : ℝ :=
  let B := eBaseDen lam x
  let T := eLogDen x
  let pn := lam*x
  let u := eParentNumerator r lam x+B-pn
  let n := (15/16)*eKNumerator r lam x-(1+lam)*u
  let c := pn*(2*u-(alpha r lam+beta r lam)*B)
  let d := (gamma r lam-delta r lam)*B^2*T-pn*eUpperNumerator r lam x*u
  let G := delta r lam*B^2*T+d*L
  4*G*(pn*n*(1+x)+eLowerNumerator r lam x*pn*beta r lam*h*(1+lam)*B) +
    4*delta r lam*eLowerNumerator r lam x*(c*T*h+d*h^2)*(1+lam)*B^2 -
    eLowerNumerator r lam x*L*c^2*(1+lam)*T

theorem eU_clear_identity (G a b delta p u k A B C T ln hn h L : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0) :
    (let P := u/B+1-p/B
     let N := (15/16)*(k/(A*B))-P
     let d := G-p/B*(hn/T)*P
     let c := p/B*(2*P-a-b)
     4*(delta+d*L)*(p/B*N+(ln/C)*(p/B*b)*h)+
       4*delta*(ln/C)*(c*h+d*h^2)-(ln/C)*L*c^2) =
    (let u1 := u+B-p
     let n1 := (15/16)*k-A*u1
     let c1 := p*(2*u1-(a+b)*B)
     let d1 := G*B^2*T-p*hn*u1
     let g1 := delta*B^2*T+d1*L
     4*g1*(p*n1*C+ln*p*b*h*A*B)+4*delta*ln*(c1*T*h+d1*h^2)*A*B^2-
       ln*L*c1^2*A*T)/(C*A*B^4*T) := by
  dsimp only
  field_simp
  ring

theorem eUFormula_quotient (r : Row) (lam x h L : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    eUFormula r lam x h L =
      eUNumerator r lam x h L/((1+x)*(1+lam)*(eBaseDen lam x)^4*eLogDen x) := by
  have hA : 0 < 1+lam := by positivity
  have hB : 0 < eBaseDen lam x := by unfold eBaseDen; positivity
  have hC : 0 < 1+x := by positivity
  have hT : 0 < eLogDen x := by unfold eLogDen; positivity
  unfold eUFormula
  rw [eParentBaseX_quotient r lam x (ne_of_gt hB), eHeavyKX_quotient,
    parentLogLower_quotient r lam x (ne_of_gt hC), parentLogUpper_quotient r lam x (ne_of_gt hT)]
  exact eU_clear_identity (gamma r lam-delta r lam) (alpha r lam) (beta r lam)
    (delta r lam) (lam*x) (eParentNumerator r lam x) (eKNumerator r lam x)
    (1+lam) (eBaseDen lam x) (1+x) (eLogDen x)
    (eLowerNumerator r lam x) (eUpperNumerator r lam x) h L
    (ne_of_gt hA) (ne_of_gt hB) (ne_of_gt hC) (ne_of_gt hT)

theorem eUFormula_response_numerator (r : Row) (lam x h L : ℝ)
    (hlo : parentLogLower r lam x ≠ 0) :
    eUFormula r lam x h L = parentLogLower r lam x *
      responseNumerator
        (eProbabilityX lam x*((15/16)*eHeavyKX r lam x-
          (eParentBaseX r lam x+1-eProbabilityX lam x))/parentLogLower r lam x)
        (eProbabilityX lam x*beta r lam)
        (eProbabilityX lam x*(2*(eParentBaseX r lam x+1-eProbabilityX lam x)-alpha r lam-beta r lam))
        (gamma r lam-delta r lam-eProbabilityX lam x*parentLogUpper r lam x*
          (eParentBaseX r lam x+1-eProbabilityX lam x)) (delta r lam) L h := by
  unfold eUFormula responseNumerator
  field_simp

theorem eUFormula_original (r : Row) (lam Y h L : ℝ) (hlam : 0 < lam) :
    eUFormula r lam (parentX lam Y) h L =
      (let P := eParentBase r lam Y+(1-p lam Y)
       let d := gamma r lam-delta r lam-p lam Y*parentLogUpper r lam (parentX lam Y)*P
       let c := p lam Y*(2*P-alpha r lam-beta r lam)
       4*(delta r lam+d*L)*(p lam Y*tangentN r lam Y 1 (3/4) P+
         parentLogLower r lam (parentX lam Y)*p lam Y*beta r lam*h)+
         4*delta r lam*parentLogLower r lam (parentX lam Y)*(c*h+d*h^2)-
         parentLogLower r lam (parentX lam Y)*L*c^2) := by
  unfold eUFormula
  rw [eProbabilityX_original lam Y hlam, eParentBaseX_original r lam Y hlam,
    eHeavyKX_original r lam Y hlam]
  unfold tangentN
  ring

end F4Heavy.Analysis
