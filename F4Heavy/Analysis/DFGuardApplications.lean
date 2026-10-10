module

public import F4Heavy.Analysis.DHFormulaD10
public import F4Heavy.Analysis.DHFormulaD11

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_lower_F_positive (lam Y z : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .D lam (parentX lam Y) ∨
      z = parentLogUpper .D lam (parentX lam Y)) :
    0 < 4*delta .D lam*(p lam Y*beta .D lam*lowerVacancy lam Y+
      (p lam Y*(2*dhParentUpper .D lam Y (lowerVacancy lam Y)-alpha .D lam-beta .D lam)+
        2*(gamma .D lam-delta .D lam-p lam Y*z*dhParentUpper .D lam Y (lowerVacancy lam Y))*dSupportVertex lam 0))-
      (11/5)*(p lam Y*(2*dhParentUpper .D lam Y (lowerVacancy lam Y)-alpha .D lam-beta .D lam)+
        2*(gamma .D lam-delta .D lam-p lam Y*z*dhParentUpper .D lam Y (lowerVacancy lam Y))*dSupportVertex lam 0)^2 := by
  have hl := inRow_activity_pos .D lam hr
  have h : 0 < dFFormula lam (parentX lam Y) z := by
    rcases hz with rfl | rfl
    · exact d_F0_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
    · exact d_F1_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  unfold dFFormula at h
  dsimp only at h
  rwa [dhVacancyX_original lam Y hl,
    dhParentUpperX_original .D lam Y (lowerVacancy lam Y) hl,
    eProbabilityX_original lam Y hl] at h

end F4Heavy.Analysis
