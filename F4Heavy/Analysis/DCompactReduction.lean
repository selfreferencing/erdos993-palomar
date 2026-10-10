module

public import F4Heavy.Analysis.DUpperPayment
public import F4Heavy.Analysis.DLowerPayment

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

-- The only remaining premises are the ten original primary response signs:
-- two lower-vacancy first vertices and eight upper-vacancy vertices.
theorem d_compactHeavy_of_primary
    (hlo : ∀ lam x z : ℝ, InRow .D lam → (5/16 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .D lam x ∨ z = parentLogUpper .D lam x) →
      0 < dhWFormula .D lam x (dhVacancyX lam x) z (dSupportVertex lam 0) 0)
    (hup : ∀ lam x z : ℝ, InRow .D lam → (5/16 : ℝ) ≤ x → x ≤ 1 →
      (z = parentLogLower .D lam x ∨ z = parentLogUpper .D lam x) →
      ∀ i : Fin 4, 0 < dhWFormula .D lam x 1 z (dSupportVertex lam i) (dSupportHeight lam i)) :
    CompactHeavy .D := by
  apply dh_compactHeavy_of_scaled_corners .D
  intro lam Y u y hr _ hx0 hx1 hu0 huq hadm rho hrho z hz
  have hl := inRow_activity_pos .D lam hr
  rcases hrho with rfl | rfl
  · apply d_lower_payment_of_primary lam Y z u y hr hx0 hx1 hz hu0 huq hadm
    have h := hlo lam (parentX lam Y) z hr hx0 hx1 hz
    rwa [dhVacancyX_original lam Y hl] at h
  · have hlog := original_parent_log_enclosure .D lam Y hr hx0 hx1
    have hz0 : 0 < z := by
      rcases hz with rfl | rfl
      · exact hlog.1
      · linarith only [hlog.1, hlog.2.1, hlog.2.2]
    have hzl : parentLogLower .D lam (parentX lam Y) ≤ z := by
      rcases hz with rfl | rfl
      · exact le_refl _
      · exact hlog.2.1.trans hlog.2.2
    exact d_upper_payment_of_primary lam Y z u y hr hx0 hx1 hz0 hzl hu0 huq hadm
      (hup lam (parentX lam Y) z hr hx0 hx1 hz)

end F4Heavy.Analysis
