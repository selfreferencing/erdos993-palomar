module

public import F4Heavy.Analysis.CapSlopeUpper
public import F4Heavy.Analysis.CapNumerator

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_nonH_parent_mass_lt_one (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hn : r ≠ .H) (hH : parentH Y ≤ q lam) : Y < 1 := by
  have hl := inRow_activity_pos r lam hr
  have hhi : lam ≤ 8 / 5 := by
    cases r with
    | D => norm_num [InRow, rowData] at hr; linarith only [hr.2]
    | E1 => norm_num [InRow, rowData] at hr; linarith only [hr.2]
    | E2 => exact hr.2
    | H => exact (hn rfl).elim
  have he : (8 : ℝ) / 3 ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 4
    norm_num [Finset.sum_range_succ] at h
    exact h
  have harg : 1 + lam < Real.exp 1 := by linarith only [he, hhi]
  have hlog := Real.log_lt_log (show 0 < 1 + lam by linarith only [hl]) harg
  rw [Real.log_exp] at hlog
  exact (cap_parent_mass_log_upper lam Y hl hH).trans_lt hlog

theorem cap_response_signs_from_scalar_bounds (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY : 0 ≤ Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho)
    (hleft : 0 < capLambda r lam (2 * (lam + 2) / (3 * lam + 4)))
    (hright : 0 < capLambda r lam 1)
    (hU : r = .H → (gamma r lam - delta r lam) * (1 + lam) / lam ≤ capParentU r lam)
    (hF : r = .H → 0 < 2 * (gamma r lam - delta r lam) * (1 + 2 * lam) / lam - alpha r lam - beta r lam +
      2 * capParentU r lam * (1 - (19 / 60 + 2 * lam / 5))) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho ∧
      ∀ u, 0 < u → u ≤ capChild lam Y →
        0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u := by
  have hlow := cap_lower_endpoint_response_positive r lam Y rho hr hY hH hrho hleft
  have hupp : 0 < capC r lam Y rho + 2 * capD r lam Y rho := by
    by_cases hY1 : Y ≤ 1
    · exact cap_upper_endpoint_response_positive_le_one r lam Y rho hr hY hY1 hrho hright
    · have he : r = .H := by
        by_contra hn
        exact hY1 (cap_nonH_parent_mass_lt_one r lam Y hr hn hH).le
      exact cap_upper_endpoint_response_positive_ge_one r lam Y rho hr hH hrho
        (le_of_lt (lt_of_not_ge hY1)) (hU he) (hF he)
  exact ⟨hupp, fun u hu huc => cap_child_response_slope_from_endpoints r lam Y rho u hr hu huc hlow hupp⟩

theorem cap_scalar_bounds_from_slope_and_increment (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho)
    (hslope : 0 < capC r lam Y rho + 2 * capD r lam Y rho ∧
      ∀ u, 0 < u → u ≤ capChild lam Y →
        0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u)
    (hincrement : ∀ u, 0 < u → u ≤ capChild lam Y →
      (childH u - childH (capChild lam Y)) / 500 ≤
        capB r lam Y rho * (childH u - childH (capChild lam Y)) + delta r lam *
        ((childH u) ^ 2 / childJ lam u -
          (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y))) :
    CapScalarBounds r lam Y rho := by
  apply cap_scalar_bounds_of_response_estimates r lam Y rho hr hY hH hrho hslope.1.le _ hincrement
  intro u hu huc
  exact ⟨cap_response_numerator_positive r lam Y rho u hr hH hrho hu huc, hslope.2 u hu huc⟩

end F4Heavy.Analysis
