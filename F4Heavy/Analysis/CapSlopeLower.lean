module

public import F4Heavy.Analysis.CapLogGeometry
public import F4Heavy.Analysis.CapFieldBounds
public import F4Heavy.Analysis.CapLogConstant

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def capParentM (r : Row) (lam : ℝ) : ℝ :=
  1 / (1 + 2 * lam) + 2 * gamma r lam / (2 + lam)

def capLambda (r : Row) (lam h : ℝ) : ℝ :=
  2 * (gamma r lam - delta r lam) * h + 2 * capParentM r lam - alpha r lam - beta r lam +
    2 * h * capParentM r lam *
      (13 / 12 - 2 * lam * capParentM r lam / (5 * (gamma r lam - delta r lam)))

theorem cap_gamma_minus_delta_pos (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < gamma r lam - delta r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [gamma, delta, field, rowData] <;> nlinarith [hr.1, hr.2]

theorem cap_parentM_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < capParentM r lam := by
  have hl := inRow_activity_pos r lam hr
  have hg := row_gamma_pos r lam hr
  unfold capParentM
  positivity

theorem cap_response_slope_lower (r : Row) (lam Y rho h : ℝ) (hr : InRow r lam)
    (hY : 0 ≤ Y) (hrho : FeasibleVacancy lam Y rho) (hh : 0 ≤ h)
    (hweight : 0 ≤ 1 - Y * h) (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) :
    capLambda r lam h ≤ (capC r lam Y rho + 2 * capD r lam Y rho * h) / p lam Y := by
  have hl := inRow_activity_pos r lam hr
  have hG := cap_gamma_minus_delta_pos r lam hr
  have hM := cap_parentM_pos r lam hr
  have hP : capParentM r lam ≤ parentP r lam Y rho := cap_parentP_lower r lam Y rho hr hY hrho
  have hPM := mul_le_mul_of_nonneg_right hP (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hweight)
  have hE := cap_exponential_tangent_lower lam (gamma r lam - delta r lam) (capParentM r lam) Y hl hG hM hlog
  have hEM := mul_le_mul_of_nonneg_left hE (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hh)
  rw [cap_response_slope_exp_identity r lam Y rho h hl]
  unfold capLambda
  have hid : 2 * lam * capParentM r lam / (5 * (gamma r lam - delta r lam)) =
      2 * (lam * capParentM r lam / (gamma r lam - delta r lam)) / 5 := by
    field_simp [ne_of_gt hG]
    <;> ring
  rw [hid]
  nlinarith only [hPM, hEM]

theorem cap_response_slope_positive_from_Lambda (r : Row) (lam Y rho h : ℝ)
    (hr : InRow r lam) (hY : 0 ≤ Y) (hrho : FeasibleVacancy lam Y rho)
    (hh : 0 ≤ h) (hweight : 0 ≤ 1 - Y * h)
    (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) (hL : 0 < capLambda r lam h) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho * h := by
  have h := hL.trans_le (cap_response_slope_lower r lam Y rho h hr hY hrho hh hweight hlog)
  exact (div_pos_iff.mp h).resolve_right (fun hn => (not_lt_of_ge (p_pos lam Y (inRow_activity_pos r lam hr)).le) hn.2) |>.1

theorem cap_height_mass_margin (lam : ℝ) (hl : 4 / 5 ≤ lam) (hu : lam ≤ 7 / 3) :
    1 / 66 ≤ 1 - (19 / 60 + 2 * lam / 5) * (2 * (lam + 2) / (3 * lam + 4)) := by
  have hd : 0 < 3 * lam + 4 := by linarith only [hl]
  have hid : 1 - (19 / 60 + 2 * lam / 5) * (2 * (lam + 2) / (3 * lam + 4)) =
      (82 + 23 * lam - 24 * lam ^ 2) / (30 * (3 * lam + 4)) := by
    field_simp
    <;> ring
  rw [hid]
  apply (le_div_iff₀ (mul_pos (by norm_num) hd)).mpr
  have hm := mul_nonneg (show 0 ≤ 7 / 3 - lam by linarith only [hu])
    (show 0 ≤ 24 * lam + 378 / 11 by linarith only [hl])
  nlinarith only [hm]

theorem cap_lower_height_parent_weight (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hlog : Real.log (5 / 2 : ℝ) < 11 / 12) :
    0 ≤ 1 - Y * (2 * (lam + 2) / (3 * lam + 4)) := by
  have hl := inRow_activity_pos r lam hr
  have hb := cap_row_activity_bounds r lam hr
  have hY := cap_parent_mass_affine_upper lam Y hl hH hlog
  have hh : 0 < 2 * (lam + 2) / (3 * lam + 4) := by positivity
  have hm := mul_le_mul_of_nonneg_right hY.le hh.le
  have hg := cap_height_mass_margin lam hb.1 hb.2
  linarith only [hm, hg]

theorem cap_response_slope_interval_positive (c d a h : ℝ)
    (ha : a ≤ h) (hh : h ≤ 1) (hleft : 0 < c + 2 * d * a) (hright : 0 < c + 2 * d) :
    0 < c + 2 * d * h := by
  by_cases hd : 0 ≤ d
  · have hm := mul_nonneg hd (sub_nonneg.mpr ha)
    nlinarith only [hm, hleft]
  · have hm := mul_nonneg (show 0 ≤ -d by linarith only [hd]) (sub_nonneg.mpr hh)
    nlinarith only [hm, hright]

theorem cap_child_response_slope_from_endpoints (r : Row) (lam Y rho u : ℝ)
    (hr : InRow r lam) (hu : 0 < u) (huc : u ≤ capChild lam Y)
    (hleft : 0 < capC r lam Y rho + 2 * capD r lam Y rho * (2 * (lam + 2) / (3 * lam + 4)))
    (hright : 0 < capC r lam Y rho + 2 * capD r lam Y rho) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u := by
  have hl := inRow_activity_pos r lam hr
  exact cap_response_slope_interval_positive _ _ _ _
    (cap_child_height_activity_lower lam Y u hl hu.le huc)
    (cap_child_height_bounds lam Y u hl hu huc).2 hleft hright

theorem cap_lower_endpoint_response_positive (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY : 0 ≤ Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho)
    (hL : 0 < capLambda r lam (2 * (lam + 2) / (3 * lam + 4))) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho * (2 * (lam + 2) / (3 * lam + 4)) := by
  have hl := inRow_activity_pos r lam hr
  exact cap_response_slope_positive_from_Lambda r lam Y rho _ hr hY hrho (by positivity)
    (cap_lower_height_parent_weight r lam Y hr hH cap_log_five_halves_upper)
    cap_log_five_halves_upper hL

theorem cap_upper_endpoint_response_positive_le_one (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1) (hrho : FeasibleVacancy lam Y rho)
    (hL : 0 < capLambda r lam 1) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho := by
  have h := cap_response_slope_positive_from_Lambda r lam Y rho 1 hr hY0 hrho
    (by norm_num) (by linarith only [hY1]) cap_log_five_halves_upper hL
  simpa only [mul_one] using h

end
end F4Heavy.Analysis
