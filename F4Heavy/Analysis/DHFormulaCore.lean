module

public import F4Heavy.Analysis.DHOriginalReduction
public import F4Heavy.Analysis.EFormulaCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dhParentBaseX (r : Row) (lam x : ℝ) : ℝ :=
  gamma r lam*(1-eProbabilityX lam x/2-(eProbabilityX lam x)^2/12)

noncomputable def dhParentUpperX (r : Row) (lam x rho : ℝ) : ℝ :=
  dhParentBaseX r lam x+(1-eProbabilityX lam x)*rho

noncomputable def dhVacancyX (lam x : ℝ) : ℝ :=
  1/(1+lam*(1-eProbabilityX lam x))

noncomputable def dhTangentX (r : Row) (x : ℝ) : ℝ :=
  match r with
  | .D => 33/40
  | .H => 1-x/8
  | _ => 3/4

noncomputable def dhNFormula (r : Row) (lam x rho : ℝ) : ℝ :=
  eHeavyKX r lam x*(2*dhTangentX r x*rho-(dhTangentX r x)^2)+
    alpha r lam*(1-rho)-dhParentUpperX r lam x rho

-- This is the original lowdegree_model.py numerator before rational clearing.
noncomputable def dhWFormula (r : Row) (lam x rho z h L : ℝ) : ℝ :=
  let P := dhParentUpperX r lam x rho
  let d := gamma r lam-delta r lam-eProbabilityX lam x*z*P
  let c := eProbabilityX lam x*(2*P-alpha r lam-beta r lam)
  4*(delta r lam+d*L)*(eProbabilityX lam x*dhNFormula r lam x rho+
    z*eProbabilityX lam x*beta r lam*rho*h)+
    4*delta r lam*z*(c*h+d*h^2)-z*L*c^2

theorem dhParentBaseX_original (r : Row) (lam Y : ℝ) (hlam : 0 < lam) :
    dhParentBaseX r lam (parentX lam Y) = dhParentBase r lam Y := by
  unfold dhParentBaseX dhParentBase
  rw [eProbabilityX_original lam Y hlam]

theorem dhParentUpperX_original (r : Row) (lam Y rho : ℝ) (hlam : 0 < lam) :
    dhParentUpperX r lam (parentX lam Y) rho = dhParentUpper r lam Y rho := by
  unfold dhParentUpperX dhParentUpper
  rw [dhParentBaseX_original r lam Y hlam, eProbabilityX_original lam Y hlam]

theorem dhVacancyX_original (lam Y : ℝ) (hlam : 0 < lam) :
    dhVacancyX lam (parentX lam Y) = lowerVacancy lam Y := by
  unfold dhVacancyX lowerVacancy
  rw [eProbabilityX_original lam Y hlam]

theorem dhTangentX_original (r : Row) (lam Y : ℝ) :
    dhTangentX r (parentX lam Y) = dhTangent r lam Y := by
  cases r <;> rfl

theorem dhNFormula_original (r : Row) (lam Y rho : ℝ) (hlam : 0 < lam) :
    dhNFormula r lam (parentX lam Y) rho =
      tangentN r lam Y rho (dhTangent r lam Y) (dhParentUpper r lam Y rho) := by
  unfold dhNFormula tangentN
  rw [eHeavyKX_original r lam Y hlam, dhTangentX_original r lam Y,
    dhParentUpperX_original r lam Y rho hlam]

theorem dhWFormula_response (r : Row) (lam x rho z h L : ℝ) (hz : z ≠ 0) :
    dhWFormula r lam x rho z h L = z*responseNumerator
      (eProbabilityX lam x*dhNFormula r lam x rho/z)
      (eProbabilityX lam x*beta r lam*rho)
      (eProbabilityX lam x*(2*dhParentUpperX r lam x rho-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-eProbabilityX lam x*z*dhParentUpperX r lam x rho)
      (delta r lam) L h := by
  unfold dhWFormula responseNumerator
  field_simp
  <;> ring

theorem dhWFormula_original_response (r : Row) (lam Y rho z h L : ℝ)
    (hlam : 0 < lam) (hz : z ≠ 0) :
    dhWFormula r lam (parentX lam Y) rho z h L = z*responseNumerator
      (p lam Y*tangentN r lam Y rho (dhTangent r lam Y) (dhParentUpper r lam Y rho)/z)
      (p lam Y*beta r lam*rho) (p lam Y*(2*dhParentUpper r lam Y rho-alpha r lam-beta r lam))
      (gamma r lam-delta r lam-p lam Y*z*dhParentUpper r lam Y rho) (delta r lam) L h := by
  rw [dhWFormula_response r lam (parentX lam Y) rho z h L hz,
    eProbabilityX_original lam Y hlam, dhNFormula_original r lam Y rho hlam,
    dhParentUpperX_original r lam Y rho hlam]

end F4Heavy.Analysis
