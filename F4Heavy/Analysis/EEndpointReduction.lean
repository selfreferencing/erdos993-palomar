module

public import F4Heavy.Analysis.EFormulaH0
public import F4Heavy.Analysis.EFormulaD

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_parent_domain_quarter (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hx : (rowData r).xMin ≤ parentX lam Y) : (1/4 : ℝ) ≤ parentX lam Y := by
  rcases he with rfl | rfl <;> exact hx

theorem e_virtual_payment_positive (r : Row) (lam Y u y : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam)
    (hx0 : (rowData r).xMin ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1) :
    0 < mixedPayment r lam Y 0 u y (3/4) (eParentBase r lam Y)
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y)) := by
  exact mixedPayment_virtual_positive r lam Y u y (3/4) (eParentBase r lam Y) _ _ hr
    (original_parent_log_enclosure r lam Y hr hx0 hx1).1
    (e_virtual_tangentN_positive r lam Y he hr hx1)
    (e_original_virtual_discriminant_positive r lam Y he hr
      ⟨e_parent_domain_quarter r lam Y he hx0, hx1⟩)

/-- The zero-vacancy discriminant is now discharged from the original source
certificate. The only remaining endpoint premise concerns vacancy one. -/
theorem e_payment_positive_of_upper_endpoint (r : Row) (lam Y rho u y : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) (hY : 0 < Y)
    (hx0 : (rowData r).xMin ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hrho : FeasibleVacancy lam Y rho)
    (hone : 0 < mixedPayment r lam Y 1 u y (3/4) (eParentBase r lam Y+(1-p lam Y))
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y))) :
    0 < payment r lam Y rho u y := by
  exact e_payment_positive_of_endpoint_certificates r lam Y rho u y he hr hY hx0 hx1 hrho
    (e_original_virtual_discriminant_positive r lam Y he hr
      ⟨e_parent_domain_quarter r lam Y he hx0, hx1⟩) hone

end F4Heavy.Analysis
