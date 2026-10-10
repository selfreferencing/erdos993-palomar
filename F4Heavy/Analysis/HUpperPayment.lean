module

public import F4Heavy.Analysis.DHFormulaCore

public import F4Heavy.Analysis.HGuardApplications
public import F4Heavy.Analysis.DHUpperResponse
public import F4Heavy.Analysis.EUpperResponse

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_upper_payment_of_primary (lam Y z u y : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz0 : 0 < z) (hz : parentLogLower .H lam (parentX lam Y) ≤ z)
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y)
    (hW : ∀ i : Fin 5, 0 < dhWFormula .H lam (parentX lam Y) 1 z
      (hUpperSupportVertex lam i) (hUpperSupportHeight lam i)) :
    0 < scaledPayment .H lam Y 1 u y (dhTangent .H lam Y) (dhParentUpper .H lam Y 1) z := by
  have hl := inRow_activity_pos .H lam hr
  have hp := p_pos lam Y hl
  have hb : 0 ≤ p lam Y*beta .H lam*1 := by
    exact mul_nonneg (mul_nonneg hp.le (row_beta_pos .H lam hr).le) (by norm_num)
  have hnum : ∀ i : Fin 5, 0 < responseNumerator
      (p lam Y*tangentN .H lam Y 1 (dhTangent .H lam Y) (dhParentUpper .H lam Y 1)/z)
      (p lam Y*beta .H lam*1)
      (p lam Y*(2*dhParentUpper .H lam Y 1-alpha .H lam-beta .H lam))
      (gamma .H lam-delta .H lam-p lam Y*z*dhParentUpper .H lam Y 1)
      (delta .H lam) (hUpperSupportHeight lam i) (hUpperSupportVertex lam i) := by
    intro i
    have h := hW i
    rw [dhWFormula_original_response .H lam Y 1 z _ _ hl (ne_of_gt hz0)] at h
    exact (mul_pos_iff_of_pos_left hz0).mp h
  obtain ⟨L, hJL, hresp⟩ := hUpper_upper_response_of_vertices lam _ _ _ _ _ u y
    hr hu0 huq hadm (row_delta_pos .H lam hr) hb
    (h_upper_curvature_negative lam Y z hr hx0 hx1 hz).le hnum
  exact scaledPayment_positive_of_response .H lam Y 1 u y (dhTangent .H lam Y)
    (dhParentUpper .H lam Y 1) z L hp hz0 (row_delta_pos .H lam hr).le hadm hJL hresp

end F4Heavy.Analysis
