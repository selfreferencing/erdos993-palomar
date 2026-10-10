module

public import F4Heavy.Analysis.DHOriginalReduction
public import F4Heavy.Analysis.DHSupportGeometry

import F4Heavy.Analysis.DHFormulaH41
import F4Heavy.Analysis.DHFormulaH42
import F4Heavy.Analysis.DHFormulaH43

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_upper_curvature_negative (lam Y z : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : parentLogLower .H lam (parentX lam Y) ≤ z) :
    gamma .H lam-delta .H lam-p lam Y*z*dhParentUpper .H lam Y 1 < 0 := by
  have hl := inRow_activity_pos .H lam hr
  have h := h_curvature_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rw [eProbabilityX_original lam Y hl, dhParentUpperX_original .H lam Y 1 hl] at h
  have hP := dh_parent_upper_positive .H lam Y 1 hr (by norm_num)
  have hm := mul_nonneg (mul_nonneg (p_pos lam Y hl).le (sub_nonneg.mpr hz)) hP.le
  nlinarith only [h, hm]

theorem h_lower_R_positive (lam Y z : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z ≤ parentLogUpper .H lam (parentX lam Y)) :
    0 < p lam Y*(2*dhParentUpper .H lam Y (lowerVacancy lam Y)-alpha .H lam-beta .H lam)+
      2*(gamma .H lam-delta .H lam-p lam Y*z*dhParentUpper .H lam Y (lowerVacancy lam Y)) := by
  have hl := inRow_activity_pos .H lam hr
  have h := h_R_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rw [eProbabilityX_original lam Y hl, dhVacancyX_original lam Y hl,
    dhParentUpperX_original .H lam Y (lowerVacancy lam Y) hl] at h
  have hP := dh_parent_upper_positive .H lam Y (lowerVacancy lam Y) hr (lowerVacancy_nonnegative lam Y hl)
  have hm := mul_nonneg (mul_nonneg (p_pos lam Y hl).le (sub_nonneg.mpr hz)) hP.le
  nlinarith only [h, hm]

theorem h_lower_C_positive (lam Y : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1) :
    0 < 4*delta .H lam-(12/5)*(p lam Y*
      (2*dhParentUpper .H lam Y (lowerVacancy lam Y)-alpha .H lam-beta .H lam)) := by
  have hl := inRow_activity_pos .H lam hr
  have h := h_C_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rwa [eProbabilityX_original lam Y hl, dhVacancyX_original lam Y hl,
    dhParentUpperX_original .H lam Y (lowerVacancy lam Y) hl] at h

end F4Heavy.Analysis
