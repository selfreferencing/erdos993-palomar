module

public import F4Heavy.Analysis.DHOriginalReduction
public import F4Heavy.Analysis.DHSupportGeometry

import F4Heavy.Analysis.DHFormulaH27
import F4Heavy.Analysis.DHFormulaH33
public import F4Heavy.Analysis.HCompactReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_lower_primary_positive (lam x z : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hz : z = parentLogLower .H lam x ∨ z = parentLogUpper .H lam x) :
    0 < dhWFormula .H lam x (dhVacancyX lam x) z (hSupportVertex lam 0) 0 := by
  rcases hz with rfl | rfl
  · exact h_LW0_primary_positive lam x hr ⟨hx0, hx1⟩
  · exact h_LW1_primary_positive lam x hr ⟨hx0, hx1⟩

theorem h_lower_corner_payment_positive (lam Y z u y : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .H lam (parentX lam Y) ∨ z = parentLogUpper .H lam (parentX lam Y))
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y) :
    0 < scaledPayment .H lam Y (lowerVacancy lam Y) u y (dhTangent .H lam Y)
      (dhParentUpper .H lam Y (lowerVacancy lam Y)) z := by
  apply h_lower_payment_of_primary lam Y z u y hr hx0 hx1 hz hu0 huq hadm
  have h := h_lower_primary_positive lam (parentX lam Y) z hr hx0 hx1 hz
  rwa [dhVacancyX_original lam Y (inRow_activity_pos .H lam hr)] at h

-- Only the ten original upper-vacancy vertex signs remain as premises.
theorem h_compactHeavy_of_upper_primary
    (hup : ∀ lam x z : ℝ, InRow .H lam → (1/4 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .H lam x ∨ z = parentLogUpper .H lam x) →
      ∀ i : Fin 5, 0 < dhWFormula .H lam x 1 z (hUpperSupportVertex lam i) (hUpperSupportHeight lam i)) :
    CompactHeavy .H := by
  exact h_compactHeavy_of_primary h_lower_primary_positive hup

end F4Heavy.Analysis
