module

public import F4Heavy.Analysis.EFieldEndpoints
public import F4Heavy.Analysis.HeavyReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem field_monotone (m0 m1 ctr : ℝ) (hm : 0 ≤ m1) : Monotone (field m0 m1 ctr) := by
  intro a b hab
  have h := mul_nonneg hm (sub_nonneg.mpr hab)
  unfold field
  nlinarith only [h]

theorem alpha_monotone (r : Row) : Monotone (alpha r) := by
  apply field_monotone
  cases r <;> norm_num [rowData]

theorem gamma_monotone (r : Row) : Monotone (gamma r) := by
  apply field_monotone
  cases r <;> norm_num [rowData]

theorem e_field_bounds (r : Row) (lam : ℝ) (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) :
    (3 / 5 : ℝ) ≤ alpha r lam ∧ alpha r lam ≤ 3 / 4 ∧
      (6 / 25 : ℝ) ≤ gamma r lam ∧ gamma r lam ≤ 1 / 3 := by
  have hal := alpha_monotone r hr.1
  have hau := alpha_monotone r hr.2
  have hgl := gamma_monotone r hr.1
  have hgu := gamma_monotone r hr.2
  rcases he with rfl | rfl
  · exact ⟨e_field_E1_a_alpha_lower.trans hal, hau.trans e_field_E1_b_alpha_upper,
      e_field_E1_a_gamma_lower.trans hgl, hgu.trans e_field_E1_b_gamma_upper⟩
  · exact ⟨e_field_E2_a_alpha_lower.trans hal, hau.trans e_field_E2_b_alpha_upper,
      e_field_E2_a_gamma_lower.trans hgl, hgu.trans e_field_E2_b_gamma_upper⟩

theorem e_activity_bounds (r : Row) (lam : ℝ) (he : r = .E1 ∨ r = .E2) (hr : InRow r lam) :
    (13 / 10 : ℝ) ≤ lam ∧ lam ≤ 8 / 5 := by
  rcases he with rfl | rfl <;> norm_num [InRow, rowData] at hr <;> constructor <;> linarith [hr.1, hr.2]

theorem heavy_probability_rational_upper (lam Y : ℝ) (hlam : 0 < lam) (hx : parentX lam Y ≤ 1) :
    p lam Y ≤ lam / (1 + 2 * lam) := by
  have h1 : 0 < 1 + lam := by linarith
  have h2 : 0 < 1 + 2 * lam := by linarith
  have hp := heavy_parent_probability_bound lam Y hlam hx
  have hscaled := mul_nonpos_of_nonneg_of_nonpos h1.le (sub_nonpos.mpr hp)
  have hid : (1 + lam) * ((1 + q lam) * p lam Y - q lam) =
      (1 + 2 * lam) * p lam Y - lam := by
    unfold q
    field_simp
    ring
  rw [hid] at hscaled
  apply (le_div_iff₀ h2).2
  nlinarith only [hscaled]

theorem e_probability_upper (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) : p lam Y ≤ 8 / 21 := by
  have hlam := inRow_activity_pos r lam hr
  have h := heavy_probability_rational_upper lam Y hlam hx
  have hbound : lam / (1 + 2 * lam) ≤ (8 / 21 : ℝ) := by
    apply (div_le_iff₀ (show 0 < 1 + 2 * lam by linarith)).2
    nlinarith only [(e_activity_bounds r lam he hr).2]
  exact h.trans hbound

theorem heavyK_upper (r : Row) (lam Y : ℝ) (hr : InRow r lam) (hx : parentX lam Y ≤ 1) :
    heavyK r lam Y ≤ (rowData r).price / (2 * (1 + lam)) := by
  have hlam := inRow_activity_pos r lam hr
  have hq := q_pos lam hlam
  have hp := heavy_parent_probability_bound lam Y hlam hx
  have hid : heavyK r lam Y = (rowData r).price / (2 * (1 + lam)) *
      ((1 + q lam) * p lam Y / q lam) := by
    unfold heavyK
    field_simp
  rw [hid]
  have hscale : 0 ≤ (rowData r).price / (2 * (1 + lam)) := by
    have := row_price_pos r
    positivity
  have hratio : (1 + q lam) * p lam Y / q lam ≤ 1 := (div_le_one hq).2 hp
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hscale

theorem e_heavyK_upper (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) : heavyK r lam Y ≤ 17 / 46 := by
  have h := heavyK_upper r lam Y hr hx
  have hprice : (rowData r).price = (17 / 10 : ℝ) := by rcases he with rfl | rfl <;> rfl
  rw [hprice] at h
  have hbound : (17 / 10 : ℝ) / (2 * (1 + lam)) ≤ 17 / 46 := by
    apply (div_le_iff₀ (by linarith only [(e_activity_bounds r lam he hr).1])).2
    nlinarith only [(e_activity_bounds r lam he hr).1]
  exact h.trans hbound

theorem e_lowerVacancy_upper (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) : lowerVacancy lam Y ≤ 50 / 89 := by
  have hlam := inRow_activity_pos r lam hr
  have hp1 := p_lt_one lam Y hlam
  have hp := e_probability_upper r lam Y he hr hx
  have hl := (e_activity_bounds r lam he hr).1
  have hprod : (13 / 10 : ℝ) * (3 / 5) ≤ lam * (1 - p lam Y) :=
    mul_le_mul hl (by linarith) (by norm_num) hlam.le
  unfold lowerVacancy
  apply (div_le_iff₀ (show 0 < 1 + lam * (1 - p lam Y) by positivity)).2
  nlinarith only [hprod]

theorem lowerVacancy_complement (lam Y : ℝ) (hlam : 0 < lam) :
    1 - lowerVacancy lam Y = lam * (1 - p lam Y) * lowerVacancy lam Y := by
  have hp1 := p_lt_one lam Y hlam
  have hd : 0 < 1 + lam * (1 - p lam Y) := by positivity
  unfold lowerVacancy
  field_simp
  ring

theorem lowerVacancy_weight_upper (lam Y : ℝ) (hlam : 0 < lam) :
    lowerVacancy lam Y * (1 - p lam Y) ≤ 1 / (1 + lam) := by
  have hp := p_pos lam Y hlam
  have hp1 := p_lt_one lam Y hlam
  have hd : 0 < 1 + lam * (1 - p lam Y) := by positivity
  have h1 : 0 < 1 + lam := by linarith
  change (1 / (1 + lam * (1 - p lam Y))) * (1 - p lam Y) ≤ _
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hd h1).2
  nlinarith only [hp]

noncomputable def eParentBase (r : Row) (lam Y : ℝ) : ℝ := gamma r lam * (1 - p lam Y / 2)

theorem eParentBase_bounds (r : Row) (lam Y : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) (hx : parentX lam Y ≤ 1) : (34 / 175 : ℝ) ≤ eParentBase r lam Y ∧
      eParentBase r lam Y ≤ 1 / 3 := by
  have hg := (e_field_bounds r lam he hr).2.2
  have hp := e_probability_upper r lam Y he hr hx
  have hp0 := p_pos lam Y (inRow_activity_pos r lam hr)
  have hg0 : 0 ≤ gamma r lam := by linarith only [hg.1]
  unfold eParentBase
  constructor
  · have h := mul_le_mul hg.1 (show (17 / 21 : ℝ) ≤ 1 - p lam Y / 2 by linarith)
      (by norm_num : (0 : ℝ) ≤ 17 / 21) hg0
    norm_num at h
    exact h
  · have h := mul_le_mul_of_nonneg_left (show 1 - p lam Y / 2 ≤ 1 by linarith) hg0
    simpa only [mul_one] using h.trans (by simpa only [mul_one] using hg.2)

end F4Heavy.Analysis
