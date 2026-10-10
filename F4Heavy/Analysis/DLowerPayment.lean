module

public import F4Heavy.Analysis.DFGuardApplications
public import F4Heavy.Analysis.DGuardApplications
public import F4Heavy.Analysis.DHLowerResponse
public import F4Heavy.Analysis.EUpperResponse

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_lower_payment_of_primary (lam Y z u y : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .D lam (parentX lam Y) ∨ z = parentLogUpper .D lam (parentX lam Y))
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y)
    (hW : 0 < dhWFormula .D lam (parentX lam Y) (lowerVacancy lam Y) z
      (dSupportVertex lam 0) 0) :
    0 < scaledPayment .D lam Y (lowerVacancy lam Y) u y (dhTangent .D lam Y)
      (dhParentUpper .D lam Y (lowerVacancy lam Y)) z := by
  have hl := inRow_activity_pos .D lam hr
  have hp := p_pos lam Y hl
  have hlog := original_parent_log_enclosure .D lam Y hr hx0 hx1
  have hz0 : 0 < z := by
    rcases hz with rfl | rfl
    · exact hlog.1
    · linarith only [hlog.1, hlog.2.1, hlog.2.2]
  have hzu : z ≤ parentLogUpper .D lam (parentX lam Y) := by
    rcases hz with rfl | rfl
    · exact hlog.2.1.trans hlog.2.2
    · exact le_refl _
  have hb : 0 ≤ p lam Y*beta .D lam*lowerVacancy lam Y :=
    mul_nonneg (mul_nonneg hp.le (row_beta_pos .D lam hr).le) (lowerVacancy_nonnegative lam Y hl)
  have hnum := hW
  rw [dhWFormula_original_response .D lam Y (lowerVacancy lam Y) z _ 0 hl (ne_of_gt hz0)] at hnum
  have hB := response_zero_vertex_positive _ _ _ _ _ _ (row_delta_pos .D lam hr)
    ((mul_pos_iff_of_pos_left hz0).mp hnum)
  rw [response_zero_envelope] at hB
  have hF := d_lower_F_positive lam Y z hr hx0 hx1 hz
  have hresp := d_lower_response_of_guards lam _ _ _ _ _ u y hr hu0 huq hadm
    (row_delta_pos .D lam hr) hb (d_lower_R_positive lam Y z hr hx0 hx1 hzu)
    (d_lower_C_positive lam Y hr hx0 hx1) hB
    (by simpa only [add_assoc] using hF.le)
  exact scaledPayment_positive_of_response .D lam Y (lowerVacancy lam Y) u y (dhTangent .D lam Y)
    (dhParentUpper .D lam Y (lowerVacancy lam Y)) z (childJ lam u) hp hz0
    (row_delta_pos .D lam hr).le hadm (le_refl _) hresp

end F4Heavy.Analysis
