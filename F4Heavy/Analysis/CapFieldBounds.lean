module

public import F4Heavy.Analysis.CapDomain
public import F4Heavy.Analysis.HeavyReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_row_activity_bounds (r : Row) (lam : ℝ) (hr : InRow r lam) :
    4 / 5 ≤ lam ∧ lam ≤ 7 / 3 := by
  cases r <;> norm_num [InRow, rowData] at hr <;> constructor <;> linarith [hr.1, hr.2]

theorem cap_row_beta_lower (r : Row) (lam : ℝ) (hr : InRow r lam) :
    1 / 8 < beta r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [beta, field, rowData] <;> nlinarith [hr.1, hr.2]

theorem cap_probability_vacancy_tenth (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    1 / 10 ≤ p lam Y * rho := by
  have hl := inRow_activity_pos r lam hr
  have hrange := cap_row_activity_bounds r lam hr
  have hden : 0 < lam ^ 2 + 3 * lam + 1 := by positivity
  have hfrac : (1 : ℝ) / 10 ≤ lam / (lam ^ 2 + 3 * lam + 1) := by
    apply (le_div_iff₀ hden).mpr
    have hprod := mul_nonneg (show 0 ≤ lam - 1 / 2 by linarith only [hrange.1])
      (show 0 ≤ 3 - lam by linarith only [hrange.2])
    nlinarith only [hprod, hrange.1]
  exact hfrac.trans (cap_probability_vacancy_lower lam Y rho hl hH hrho)

theorem cap_b_uniform_lower (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    1 / 500 ≤ capB r lam Y rho := by
  have hbeta := cap_row_beta_lower r lam hr
  have hp := cap_probability_vacancy_tenth r lam Y rho hr hH hrho
  have hm := mul_le_mul (show (1 : ℝ) / 8 ≤ beta r lam by linarith only [hbeta]) hp
    (by norm_num : (0 : ℝ) ≤ 1 / 10) (by linarith only [hbeta] : 0 ≤ beta r lam)
  unfold capB
  nlinarith only [hm]

/-- All elementary domain and field obligations are discharged here.
Only the two response signs and the reserve increment remain regional. -/
theorem cap_scalar_bounds_of_response_estimates (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho)
    (hzero : 0 ≤ capC r lam Y rho + 2 * capD r lam Y rho)
    (hresponse : ∀ u, 0 < u → u ≤ capChild lam Y →
      0 < 2 * delta r lam * childH u - capC r lam Y rho * childJ lam u ∧
      0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u)
    (hincrement : ∀ u, 0 < u → u ≤ capChild lam Y →
      (childH u - childH (capChild lam Y)) / 500 ≤
        capB r lam Y rho * (childH u - childH (capChild lam Y)) + delta r lam *
        ((childH u) ^ 2 / childJ lam u -
          (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y))) :
    CapScalarBounds r lam Y rho := by
  have hl := inRow_activity_pos r lam hr
  refine ⟨cap_child_pos lam Y hl hY, (row_delta_pos r lam hr).le,
    cap_b_uniform_lower r lam Y rho hr hH hrho, hzero, ?_, ?_, hincrement⟩
  · intro u hu huc
    have hh := cap_child_height_bounds lam Y u hl hu huc
    exact ⟨hh.1, hh.2, cap_child_reserve_pos lam Y u hl hu huc, hresponse u hu huc⟩
  · intro u hu huc
    exact cap_height_increment_on_domain lam Y u hl hu huc

end F4Heavy.Analysis
