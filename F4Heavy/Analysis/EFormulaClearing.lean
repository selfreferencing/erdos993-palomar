module

public import F4Heavy.Analysis.EFormulaCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eBaseDen (lam x : ℝ) : ℝ := 1+lam+lam*x
noncomputable def eLogDen (x : ℝ) : ℝ := 9*x^2+12*x+1
noncomputable def eLowerNumerator (r : Row) (lam x : ℝ) : ℝ :=
  (1+x)*activityLogLower r lam+2*(1-x)
noncomputable def eUpperNumerator (r : Row) (lam x : ℝ) : ℝ :=
  eLogDen x*(activityLogUpper r lam+1386294361120/1000000000000-21/73)-3*(9*x^2-1)
noncomputable def eParentNumerator (r : Row) (lam x : ℝ) : ℝ :=
  gamma r lam*(2*eBaseDen lam x-lam*x)/2
noncomputable def eKNumerator (r : Row) (lam x : ℝ) : ℝ :=
  (rowData r).price*(1+2*lam)*x/2
noncomputable def eH0Numerator (r : Row) (lam x : ℝ) : ℝ :=
  let B := eBaseDen lam x
  let T := eLogDen x
  let u := eParentNumerator r lam x
  let d := (gamma r lam-delta r lam)*B^2*T-lam*x*eUpperNumerator r lam x*u
  let c := alpha r lam*(1+lam)*B-(1+lam)*u-(9/16)*eKNumerator r lam x
  4*d*c*(1+x)-lam*x*eLowerNumerator r lam x*(2*u-(alpha r lam+beta r lam)*B)^2*(1+lam)*T
noncomputable def eDNumerator (r : Row) (lam x : ℝ) : ℝ :=
  lam*x*eUpperNumerator r lam x*(eParentNumerator r lam x+eBaseDen lam x-lam*x) -
    (gamma r lam-delta r lam)*(eBaseDen lam x)^2*eLogDen x

theorem eParentBaseX_quotient (r : Row) (lam x : ℝ) (hB : eBaseDen lam x ≠ 0) :
    eParentBaseX r lam x = eParentNumerator r lam x/eBaseDen lam x := by
  unfold eParentBaseX eProbabilityX eParentNumerator eBaseDen at *
  field_simp

theorem eHeavyKX_quotient (r : Row) (lam x : ℝ) :
    eHeavyKX r lam x = eKNumerator r lam x/((1+lam)*eBaseDen lam x) := by
  unfold eHeavyKX eKNumerator eBaseDen
  rw [show 2*(1+lam)*(1+lam+lam*x) = 2*((1+lam)*(1+lam+lam*x)) by ring, ← div_div]

theorem parentLogLower_quotient (r : Row) (lam x : ℝ) (hC : 1+x ≠ 0) :
    parentLogLower r lam x = eLowerNumerator r lam x/(1+x) := by
  unfold parentLogLower eLowerNumerator
  field_simp

theorem parentLogUpper_quotient (r : Row) (lam x : ℝ) (hT : eLogDen x ≠ 0) :
    parentLogUpper r lam x = eUpperNumerator r lam x/eLogDen x := by
  apply (eq_div_iff hT).mpr
  change (activityLogUpper r lam + (1386294361120/1000000000000-21/73-
    3*(9*x^2-1)/eLogDen x))*eLogDen x =
    eLogDen x*(activityLogUpper r lam+1386294361120/1000000000000-21/73)-3*(9*x^2-1)
  rw [add_mul, sub_mul, sub_mul, div_mul_cancel₀ _ hT]
  ring

theorem eH0_clear_identity (G a b p u k A B C T ln hn : ℝ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hT : T ≠ 0) :
    4*(G-p/B*(hn/T)*(u/B))*(a-u/B-(9/16)*(k/(A*B)))-
      p/B*(ln/C)*(2*(u/B)-a-b)^2 =
      (4*(G*B^2*T-p*hn*u)*(a*A*B-A*u-(9/16)*k)*C -
        p*ln*(2*u-(a+b)*B)^2*A*T)/(A*B^3*T*C) := by
  field_simp
  ring

theorem eD_clear_identity (G p u B T hn : ℝ) (hB : B ≠ 0) (hT : T ≠ 0) :
    p/B*(hn/T)*(u/B+1-p/B)-G = (p*hn*(u+B-p)-G*B^2*T)/(B^2*T) := by
  field_simp

theorem eH0Formula_quotient (r : Row) (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    eH0Formula r lam x = eH0Numerator r lam x/((1+lam)*(eBaseDen lam x)^3*eLogDen x*(1+x)) := by
  have hA : 0 < 1+lam := by positivity
  have hB : 0 < eBaseDen lam x := by unfold eBaseDen; positivity
  have hC : 0 < 1+x := by positivity
  have hT : 0 < eLogDen x := by unfold eLogDen; positivity
  unfold eH0Formula
  rw [eParentBaseX_quotient r lam x (ne_of_gt hB), eHeavyKX_quotient,
    parentLogLower_quotient r lam x (ne_of_gt hC), parentLogUpper_quotient r lam x (ne_of_gt hT)]
  exact eH0_clear_identity (gamma r lam-delta r lam) (alpha r lam) (beta r lam)
    (lam*x) (eParentNumerator r lam x) (eKNumerator r lam x)
    (1+lam) (eBaseDen lam x) (1+x) (eLogDen x) (eLowerNumerator r lam x) (eUpperNumerator r lam x)
    (ne_of_gt hA) (ne_of_gt hB) (ne_of_gt hC) (ne_of_gt hT)

theorem eDFormula_quotient (r : Row) (lam x : ℝ) (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    eDFormula r lam x = eDNumerator r lam x/((eBaseDen lam x)^2*eLogDen x) := by
  have hB : 0 < eBaseDen lam x := by unfold eBaseDen; positivity
  have hT : 0 < eLogDen x := by unfold eLogDen; positivity
  unfold eDFormula
  rw [eParentBaseX_quotient r lam x (ne_of_gt hB), parentLogUpper_quotient r lam x (ne_of_gt hT)]
  exact eD_clear_identity (gamma r lam-delta r lam) (lam*x) (eParentNumerator r lam x)
    (eBaseDen lam x) (eLogDen x) (eUpperNumerator r lam x) (ne_of_gt hB) (ne_of_gt hT)

end F4Heavy.Analysis
