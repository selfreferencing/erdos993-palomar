module

public import F4Heavy.Analysis.ESign

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def eProbabilityX (lam x : ℝ) : ℝ := lam*x/(1+lam+lam*x)

noncomputable def eHeavyKX (r : Row) (lam x : ℝ) : ℝ :=
  (rowData r).price*(1+2*lam)*x/(2*(1+lam)*(1+lam+lam*x))

noncomputable def eParentBaseX (r : Row) (lam x : ℝ) : ℝ :=
  gamma r lam*(1-eProbabilityX lam x/2)

noncomputable def eH0Formula (r : Row) (lam x : ℝ) : ℝ :=
  4*(gamma r lam-delta r lam-eProbabilityX lam x*parentLogUpper r lam x*eParentBaseX r lam x)*
    (alpha r lam-eParentBaseX r lam x-(9/16)*eHeavyKX r lam x) -
  eProbabilityX lam x*parentLogLower r lam x*(2*eParentBaseX r lam x-alpha r lam-beta r lam)^2

noncomputable def eDFormula (r : Row) (lam x : ℝ) : ℝ :=
  eProbabilityX lam x*parentLogUpper r lam x*(eParentBaseX r lam x+1-eProbabilityX lam x) -
    (gamma r lam-delta r lam)

theorem eProbabilityX_original (lam Y : ℝ) (hlam : 0 < lam) :
    eProbabilityX lam (parentX lam Y) = p lam Y := by
  have hB : 0 < 1+lam*Real.exp (-Y) := by positivity
  have hl : 0 < 1+lam := by positivity
  unfold eProbabilityX parentX p
  have hd : 1+lam+lam*((1+lam)*Real.exp (-Y)) = (1+lam)*(1+lam*Real.exp (-Y)) := by ring
  rw [hd]
  field_simp

theorem eHeavyKX_original (r : Row) (lam Y : ℝ) (hlam : 0 < lam) :
    eHeavyKX r lam (parentX lam Y) = heavyK r lam Y := by
  have hB : 0 < 1+lam*Real.exp (-Y) := by positivity
  have hl : 0 < 1+lam := by positivity
  unfold eHeavyKX parentX heavyK p q
  have hd : 1+lam+lam*((1+lam)*Real.exp (-Y)) = (1+lam)*(1+lam*Real.exp (-Y)) := by ring
  rw [hd]
  field_simp
  ring

theorem eParentBaseX_original (r : Row) (lam Y : ℝ) (hlam : 0 < lam) :
    eParentBaseX r lam (parentX lam Y) = eParentBase r lam Y := by
  unfold eParentBaseX eParentBase
  rw [eProbabilityX_original lam Y hlam]

theorem eH0Formula_original (r : Row) (lam Y : ℝ) (hlam : 0 < lam) :
    eH0Formula r lam (parentX lam Y) =
      4*(gamma r lam-delta r lam-p lam Y*parentLogUpper r lam (parentX lam Y)*eParentBase r lam Y)*
        tangentN r lam Y 0 (3/4) (eParentBase r lam Y) -
      p lam Y*parentLogLower r lam (parentX lam Y)*(2*eParentBase r lam Y-alpha r lam-beta r lam)^2 := by
  unfold eH0Formula
  rw [eProbabilityX_original lam Y hlam, eParentBaseX_original r lam Y hlam, eHeavyKX_original r lam Y hlam]
  unfold tangentN
  ring

theorem eDFormula_original (r : Row) (lam Y : ℝ) (hlam : 0 < lam) :
    eDFormula r lam (parentX lam Y) =
      p lam Y*parentLogUpper r lam (parentX lam Y)*(eParentBase r lam Y+(1-p lam Y)) -
        (gamma r lam-delta r lam) := by
  unfold eDFormula
  rw [eProbabilityX_original lam Y hlam, eParentBaseX_original r lam Y hlam]
  ring

end F4Heavy.Analysis
