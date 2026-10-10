module

public import F4Heavy.Analysis.DHOriginalReduction
public import F4Heavy.Analysis.DHSupportGeometry

import F4Heavy.Analysis.DHFormulaH39
import F4Heavy.Analysis.DHFormulaH40

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_lower_F_positive (lam Y z : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .H lam (parentX lam Y) ∨
      z = parentLogUpper .H lam (parentX lam Y)) :
    0 < 4*delta .H lam*(p lam Y*beta .H lam*lowerVacancy lam Y+
      (p lam Y*(2*dhParentUpper .H lam Y (lowerVacancy lam Y)-alpha .H lam-beta .H lam)+
        2*(gamma .H lam-delta .H lam-p lam Y*z*dhParentUpper .H lam Y (lowerVacancy lam Y))*hSupportVertex lam 0))-
      (12/5)*(p lam Y*(2*dhParentUpper .H lam Y (lowerVacancy lam Y)-alpha .H lam-beta .H lam)+
        2*(gamma .H lam-delta .H lam-p lam Y*z*dhParentUpper .H lam Y (lowerVacancy lam Y))*hSupportVertex lam 0)^2 := by
  have hl := inRow_activity_pos .H lam hr
  have h : 0 < hFFormula lam (parentX lam Y) z := by
    rcases hz with rfl | rfl
    · exact h_F0_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
    · exact h_F1_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  unfold hFFormula at h
  dsimp only at h
  rwa [dhVacancyX_original lam Y hl,
    dhParentUpperX_original .H lam Y (lowerVacancy lam Y) hl,
    eProbabilityX_original lam Y hl] at h

end F4Heavy.Analysis
