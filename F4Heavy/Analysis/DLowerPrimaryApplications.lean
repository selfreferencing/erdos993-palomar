module

public import F4Heavy.Analysis.DHFormulaD00
public import F4Heavy.Analysis.DHFormulaD05
public import F4Heavy.Analysis.DCompactReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_lower_primary_positive (lam x z : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hz : z = parentLogLower .D lam x ∨ z = parentLogUpper .D lam x) :
    0 < dhWFormula .D lam x (dhVacancyX lam x) z (dSupportVertex lam 0) 0 := by
  rcases hz with rfl | rfl
  · exact d_LW0_primary_positive lam x hr ⟨hx0, hx1⟩
  · exact d_LW1_primary_positive lam x hr ⟨hx0, hx1⟩

theorem d_lower_corner_payment_positive (lam Y z u y : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hz : z = parentLogLower .D lam (parentX lam Y) ∨ z = parentLogUpper .D lam (parentX lam Y))
    (hu0 : 0 ≤ u) (huq : u ≤ q lam) (hadm : Admissible lam u y) :
    0 < scaledPayment .D lam Y (lowerVacancy lam Y) u y (dhTangent .D lam Y)
      (dhParentUpper .D lam Y (lowerVacancy lam Y)) z := by
  apply d_lower_payment_of_primary lam Y z u y hr hx0 hx1 hz hu0 huq hadm
  have h := d_lower_primary_positive lam (parentX lam Y) z hr hx0 hx1 hz
  rwa [dhVacancyX_original lam Y (inRow_activity_pos .D lam hr)] at h

-- Only the eight original upper-vacancy vertex signs remain as premises.
theorem d_compactHeavy_of_upper_primary
    (hup : ∀ lam x z : ℝ, InRow .D lam → (5/16 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .D lam x ∨ z = parentLogUpper .D lam x) →
      ∀ i : Fin 4, 0 < dhWFormula .D lam x 1 z (dSupportVertex lam i) (dSupportHeight lam i)) :
    CompactHeavy .D := by
  exact d_compactHeavy_of_primary d_lower_primary_positive hup

end F4Heavy.Analysis
