module

public import F4Heavy.Analysis.EPhysicalBounds
public import F4Heavy.Analysis.MixedLogPayment
public import F4Heavy.Analysis.ParentBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem e_tangentN_lower_negative (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) :
    tangentN r lam Y (lowerVacancy lam Y) (3 / 4)
      (eParentBase r lam Y + (1 - p lam Y) * lowerVacancy lam Y) < 0 := by
  have hlam := inRow_activity_pos r lam hr
  have hp1 := p_lt_one lam Y hlam
  have hR0 : 0 < lowerVacancy lam Y := by unfold lowerVacancy; positivity
  have hR : lowerVacancy lam Y ≤ (9 / 16 : ℝ) := by
    linarith only [e_lowerVacancy_upper r lam Y he hr hx]
  have hK0 := (heavyK_pos r lam Y hr).le
  have hK : heavyK r lam Y ≤ (3 / 8 : ℝ) := by
    linarith only [e_heavyK_upper r lam Y he hr hx]
  have hfirst : heavyK r lam Y * (3 / 2 * lowerVacancy lam Y - 9 / 16) ≤ 27 / 256 := by
    have h := mul_le_mul_of_nonneg_left
      (show 3 / 2 * lowerVacancy lam Y - 9 / 16 ≤ (9 / 32 : ℝ) by linarith only [hR]) hK0
    nlinarith only [h, hK]
  have hw : lowerVacancy lam Y * (1 - p lam Y) ≤ (10 / 23 : ℝ) := by
    apply (lowerVacancy_weight_upper lam Y hlam).trans
    apply (div_le_iff₀ (show 0 < 1 + lam by linarith)).2
    nlinarith only [(e_activity_bounds r lam he hr).1]
  have ha := (e_field_bounds r lam he hr).2.1
  have hal : alpha r lam * lam - 1 ≤ (1 / 5 : ℝ) := by
    have h := mul_le_mul ha (e_activity_bounds r lam he hr).2 hlam.le (by norm_num : (0 : ℝ) ≤ 3 / 4)
    nlinarith only [h]
  have hsecond : lowerVacancy lam Y * (1 - p lam Y) * (alpha r lam * lam - 1) ≤ 2 / 23 := by
    have h := mul_le_mul_of_nonneg_left hal (mul_nonneg hR0.le (sub_nonneg.mpr hp1.le))
    nlinarith only [h, hw]
  have hid : tangentN r lam Y (lowerVacancy lam Y) (3 / 4)
      (eParentBase r lam Y + (1 - p lam Y) * lowerVacancy lam Y) =
      heavyK r lam Y * (3 / 2 * lowerVacancy lam Y - 9 / 16) +
      lowerVacancy lam Y * (1 - p lam Y) * (alpha r lam * lam - 1) - eParentBase r lam Y := by
    unfold tangentN
    rw [lowerVacancy_complement lam Y hlam]
    ring
  rw [hid]
  linarith only [hfirst, hsecond, (eParentBase_bounds r lam Y he hr hx).1]

theorem e_tangentN_one_negative (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) :
    tangentN r lam Y 1 (3 / 4) (eParentBase r lam Y + (1 - p lam Y)) < 0 := by
  have hK := e_heavyK_upper r lam Y he hr hx
  have hp := e_probability_upper r lam Y he hr hx
  have hP := (eParentBase_bounds r lam Y he hr hx).1
  unfold tangentN
  nlinarith only [hK, hp, hP]

theorem e_tangentN_negative (r : Row) (lam Y rho : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) (hrho : FeasibleVacancy lam Y rho) :
    tangentN r lam Y rho (3 / 4) (eParentBase r lam Y + (1 - p lam Y) * rho) < 0 := by
  have hlo := e_tangentN_lower_negative r lam Y he hr hx
  have hhi := e_tangentN_one_negative r lam Y he hr hx
  unfold tangentN at *
  by_cases hs : 0 ≤ 3 / 2 * heavyK r lam Y - alpha r lam - (1 - p lam Y)
  · have h := mul_nonneg hs (sub_nonneg.mpr hrho.2)
    nlinarith only [h, hhi]
  · have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hs) (sub_nonneg.mpr hrho.1)
    nlinarith only [h, hlo]

theorem e_virtual_tangentN_positive (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) :
    0 < tangentN r lam Y 0 (3 / 4) (eParentBase r lam Y) := by
  have ha := (e_field_bounds r lam he hr).1
  have hK := e_heavyK_upper r lam Y he hr hx
  have hP := (eParentBase_bounds r lam Y he hr hx).2
  unfold tangentN
  nlinarith only [ha, hK, hP]

theorem e_linear_parent_majorant (r : Row) (lam Y rho : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) (hrho : FeasibleVacancy lam Y rho) :
    parentP r lam Y rho ≤ eParentBase r lam Y + (1 - p lam Y) * rho ∧
      0 < eParentBase r lam Y + (1 - p lam Y) * rho := by
  constructor
  · simpa only [eParentBase, add_comm, mul_comm] using parentP_linear_upper r lam Y rho hr
  · have hp := p_lt_one lam Y (inRow_activity_pos r lam hr)
    have hrp := feasible_vacancy_pos lam Y rho (inRow_activity_pos r lam hr) hrho
    have hb := (eParentBase_bounds r lam Y he hr hx).1
    have h := mul_pos (sub_pos.mpr hp) hrp
    linarith only [hb, h]

theorem e_payment_positive_of_endpoint_certificates (r : Row) (lam Y rho u y : ℝ)
    (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) (hY : 0 < Y)
    (hx0 : (rowData r).xMin ≤ parentX lam Y) (hx1 : parentX lam Y ≤ 1)
    (hrho : FeasibleVacancy lam Y rho)
    (hdisc : 0 < 4 * (gamma r lam - delta r lam - p lam Y *
        parentLogUpper r lam (parentX lam Y) * eParentBase r lam Y) *
        tangentN r lam Y 0 (3 / 4) (eParentBase r lam Y) -
        p lam Y * parentLogLower r lam (parentX lam Y) *
        (2 * eParentBase r lam Y - alpha r lam - beta r lam) ^ 2)
    (hone : 0 < mixedPayment r lam Y 1 u y (3 / 4) (eParentBase r lam Y + (1 - p lam Y))
      (parentLogLower r lam (parentX lam Y)) (parentLogUpper r lam (parentX lam Y))) :
    0 < payment r lam Y rho u y := by
  have hP := e_linear_parent_majorant r lam Y rho he hr hx1 hrho
  apply payment_positive_of_mixed_endpoints r lam Y rho u y (3 / 4)
    (eParentBase r lam Y) (1 - p lam Y) hr hY hrho hx0 hx1 hP.1 hP.2.le
    (e_tangentN_negative r lam Y rho he hr hx1 hrho).le _ hone
  exact mixedPayment_virtual_positive r lam Y u y (3 / 4) (eParentBase r lam Y) _ _ hr
    (original_parent_log_enclosure r lam Y hr hx0 hx1).1
    (e_virtual_tangentN_positive r lam Y he hr hx1) hdisc

end F4Heavy.Analysis
