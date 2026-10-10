module

public import F4Heavy.Analysis.DHFormulaD12
public import F4Heavy.Analysis.DHFormulaD13
public import F4Heavy.Analysis.DHFormulaD14

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_upper_curvature_negative (lam Y z : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : parentLogLower .D lam (parentX lam Y) ≤ z) :
    gamma .D lam-delta .D lam-p lam Y*z*dhParentUpper .D lam Y 1 < 0 := by
  have hl := inRow_activity_pos .D lam hr
  have h := d_curvature_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rw [eProbabilityX_original lam Y hl, dhParentUpperX_original .D lam Y 1 hl] at h
  have hP := dh_parent_upper_positive .D lam Y 1 hr (by norm_num)
  have hm := mul_nonneg (mul_nonneg (p_pos lam Y hl).le (sub_nonneg.mpr hz)) hP.le
  nlinarith only [h, hm]

theorem d_lower_R_positive (lam Y z : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z ≤ parentLogUpper .D lam (parentX lam Y)) :
    0 < p lam Y*(2*dhParentUpper .D lam Y (lowerVacancy lam Y)-alpha .D lam-beta .D lam)+
      2*(gamma .D lam-delta .D lam-p lam Y*z*dhParentUpper .D lam Y (lowerVacancy lam Y)) := by
  have hl := inRow_activity_pos .D lam hr
  have h := d_R_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rw [eProbabilityX_original lam Y hl, dhVacancyX_original lam Y hl,
    dhParentUpperX_original .D lam Y (lowerVacancy lam Y) hl] at h
  have hP := dh_parent_upper_positive .D lam Y (lowerVacancy lam Y) hr (lowerVacancy_nonnegative lam Y hl)
  have hm := mul_nonneg (mul_nonneg (p_pos lam Y hl).le (sub_nonneg.mpr hz)) hP.le
  nlinarith only [h, hm]

theorem d_lower_C_positive (lam Y : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1) :
    0 < 4*delta .D lam-(11/5)*(p lam Y*
      (2*dhParentUpper .D lam Y (lowerVacancy lam Y)-alpha .D lam-beta .D lam)) := by
  have hl := inRow_activity_pos .D lam hr
  have h := d_C_guard_positive lam (parentX lam Y) hr ⟨hx0, hx1⟩
  rwa [eProbabilityX_original lam Y hl, dhVacancyX_original lam Y hl,
    dhParentUpperX_original .D lam Y (lowerVacancy lam Y) hl] at h

end F4Heavy.Analysis
