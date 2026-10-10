module

public import F4Heavy.Analysis.DHFormulaCore

public import F4Heavy.Analysis.HFGuardApplications
public import F4Heavy.Analysis.HGuardApplications
public import F4Heavy.Analysis.DHLowerResponse
public import F4Heavy.Analysis.EUpperResponse

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_lower_payment_of_primary (lam Y z u y : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .H lam (parentX lam Y) ∨ z = parentLogUpper .H lam (parentX lam Y))
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y)
    (hW : 0 < dhWFormula .H lam (parentX lam Y) (lowerVacancy lam Y) z
      (hSupportVertex lam 0) 0) :
    0 < scaledPayment .H lam Y (lowerVacancy lam Y) u y (dhTangent .H lam Y)
      (dhParentUpper .H lam Y (lowerVacancy lam Y)) z := by
  have hl := inRow_activity_pos .H lam hr
  have hp := p_pos lam Y hl
  have hlog := original_parent_log_enclosure .H lam Y hr hx0 hx1
  have hz0 : 0 < z := by
    rcases hz with rfl | rfl
    · exact hlog.1
    · linarith only [hlog.1, hlog.2.1, hlog.2.2]
  have hzu : z ≤ parentLogUpper .H lam (parentX lam Y) := by
    rcases hz with rfl | rfl
    · exact hlog.2.1.trans hlog.2.2
    · exact le_refl _
  have hb : 0 ≤ p lam Y*beta .H lam*lowerVacancy lam Y :=
    mul_nonneg (mul_nonneg hp.le (row_beta_pos .H lam hr).le) (lowerVacancy_nonnegative lam Y hl)
  have hnum := hW
  rw [dhWFormula_original_response .H lam Y (lowerVacancy lam Y) z _ 0 hl (ne_of_gt hz0)] at hnum
  have hB := response_zero_vertex_positive _ _ _ _ _ _ (row_delta_pos .H lam hr)
    ((mul_pos_iff_of_pos_left hz0).mp hnum)
  rw [response_zero_envelope] at hB
  have hF := h_lower_F_positive lam Y z hr hx0 hx1 hz
  have hresp := h_lower_response_of_guards lam _ _ _ _ _ u y hr hu0 huq hadm
    (row_delta_pos .H lam hr) hb (h_lower_R_positive lam Y z hr hx0 hx1 hzu)
    (h_lower_C_positive lam Y hr hx0 hx1) hB
    (by simpa only [add_assoc] using hF.le)
  exact scaledPayment_positive_of_response .H lam Y (lowerVacancy lam Y) u y (dhTangent .H lam Y)
    (dhParentUpper .H lam Y (lowerVacancy lam Y)) z (childJ lam u) hp hz0
    (row_delta_pos .H lam hr).le hadm (le_refl _) hresp

end F4Heavy.Analysis
