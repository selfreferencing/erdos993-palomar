module

public import F4Heavy.Analysis.HUpperPayment
public import F4Heavy.Analysis.HLowerPayment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

-- The only remaining premises are the twelve original primary response signs:
-- two lower-vacancy first vertices and ten upper-vacancy vertices.
theorem h_compactHeavy_of_primary
    (hlo : ∀ lam x z : ℝ, InRow .H lam → (1/4 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .H lam x ∨ z = parentLogUpper .H lam x) →
      0 < dhWFormula .H lam x (dhVacancyX lam x) z (hSupportVertex lam 0) 0)
    (hup : ∀ lam x z : ℝ, InRow .H lam → (1/4 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .H lam x ∨ z = parentLogUpper .H lam x) →
      ∀ i : Fin 5, 0 < dhWFormula .H lam x 1 z (hUpperSupportVertex lam i) (hUpperSupportHeight lam i)) :
    CompactHeavy .H := by
  apply dh_compactHeavy_of_scaled_corners .H
  intro lam Y u y hr _ hx0 hx1 hu0 huq hadm rho hrho z hz
  have hl := inRow_activity_pos .H lam hr
  rcases hrho with rfl | rfl
  · apply h_lower_payment_of_primary lam Y z u y hr hx0 hx1 hz hu0 huq hadm
    have h := hlo lam (parentX lam Y) z hr hx0 hx1 hz
    rwa [dhVacancyX_original lam Y hl] at h
  · have hlog := original_parent_log_enclosure .H lam Y hr hx0 hx1
    have hz0 : 0 < z := by
      rcases hz with rfl | rfl
      · exact hlog.1
      · linarith only [hlog.1, hlog.2.1, hlog.2.2]
    have hzl : parentLogLower .H lam (parentX lam Y) ≤ z := by
      rcases hz with rfl | rfl
      · exact le_refl _
      · exact hlog.2.1.trans hlog.2.2
    exact h_upper_payment_of_primary lam Y z u y hr hx0 hx1 hz0 hzl hu0 huq hadm
      (hup lam (parentX lam Y) z hr hx0 hx1 hz)

end F4Heavy.Analysis
