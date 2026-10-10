module

public import F4Heavy.Analysis.TailCurvatureDerivatives
public import F4Heavy.Analysis.TailQuadraticLower

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_gamma_minus_delta_positive (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < gamma r lam - delta r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [gamma, delta, field, rowData] <;> nlinarith [hr.1, hr.2]

theorem tail_second_derivative_lower (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (h1 : 0 < tailGuard r lam 1) (h2 : 0 < tailGuard r lam 2)
    (hY : tailTau r lam ≤ Y) : tailLStar r lam ≤ tailCurvatureSecond r lam Y := by
  have hl := inRow_activity_pos r lam hr
  have hg := row_gamma_pos r lam hr
  have hG := tail_gamma_minus_delta_positive r lam hr
  have hp := p_pos lam Y hl
  have hp1 := p_lt_one lam Y hl
  have hspos : 0 < tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact p_pos lam _ hl
  have hs6 : tailPStar r lam < 1 / 6 := by change 0 < 1 / 6 - tailPStar r lam at h1; linarith only [h1]
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact tail_probability_antitone lam (tailTau r lam) Y hl hY
  have hY0 : 0 ≤ Y := by have ht := tail_threshold_lower_of_guard r lam hr h2; linarith only [ht, hY]
  have harg : 0 < tailScale r * (1 + lam) := mul_pos (tail_scale_positive r) (by linarith)
  have hexp : tailScale r * (1 + lam) ≤ Real.exp Y := by
    have h := Real.exp_le_exp.mpr hY
    simpa only [tailTau, Real.exp_log harg] using h
  have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hG.le) hl.le
  have heb : tailEStar r lam ≤ (gamma r lam - delta r lam) * Real.exp Y / lam := by
    simpa only [tailEStar, mul_assoc] using he
  have ha0 : 0 ≤ 1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 := by positivity
  have ha : 1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 ≤ tailAStar r lam := by
    unfold tailAStar
    have h := mul_le_mul_of_nonneg_left hpstar hg.le
    linarith only [h]
  have ha1 : 0 ≤ tailAStar r lam := ha0.trans ha
  have hw0 : 0 ≤ p lam Y * (1 - p lam Y) := mul_nonneg hp.le (sub_nonneg.mpr hp1.le)
  have hw : p lam Y * (1 - p lam Y) ≤ tailPStar r lam := by nlinarith only [hpstar, sq_nonneg (p lam Y)]
  have hb := (mul_le_mul_of_nonneg_left ha hw0).trans (mul_le_mul_of_nonneg_right hw ha1)
  have hrest : 0 ≤ Y * p lam Y * (1 - p lam Y) *
      ((1 - 2 * p lam Y) * (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6) +
        gamma r lam * p lam Y * (1 - p lam Y) / 6) := by
    have hsmall : 0 ≤ 1 - 2 * p lam Y := by linarith only [hpstar, hs6]
    positivity
  unfold tailLStar tailCurvatureSecond
  nlinarith only [heb, hb, hrest]

theorem tail_threshold_slope_lower (r : Row) (lam : ℝ) (hr : InRow r lam)
    (h1 : 0 < tailGuard r lam 1) (h9 : 0 < tailGuard r lam 9) :
    -tailEta r ≤ tailCurvatureSlope r lam (tailTau r lam) := by
  have hl := inRow_activity_pos r lam hr
  have hg := row_gamma_pos r lam hr
  have hspos : 0 < tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact p_pos lam _ hl
  have hs1 : tailPStar r lam < 1 := by change 0 < 1 / 6 - tailPStar r lam at h1; linarith only [h1]
  have ha0 : 0 ≤ tailAStar r lam := by unfold tailAStar; positivity
  have hm := mul_le_mul_of_nonneg_right (tail_threshold_bounds r lam hr).2
    (mul_nonneg (mul_nonneg hspos.le (sub_nonneg.mpr hs1.le)) ha0)
  rw [tail_curvature_threshold_slope r lam hl]
  change 0 < tailEStar r lam - tailP1 r lam (tailPStar r lam) -
    tailTauHi r lam * tailPStar r lam * (1 - tailPStar r lam) * tailAStar r lam + tailEta r at h9
  nlinarith only [hm, h9]

theorem tail_curvature_lower_of_guards (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) (h1 : 0 < tailGuard r lam 1)
    (h2 : 0 < tailGuard r lam 2) (h8 : 0 < tailGuard r lam 8)
    (h9 : 0 < tailGuard r lam 9) :
    tailD r lam ≤ (gamma r lam - delta r lam) / p lam Y - Y * tailP1 r lam (p lam Y) := by
  have hl := inRow_activity_pos r lam hr
  have hg := row_gamma_pos r lam hr
  have hdrop := tail_curvature_drop_bound (tailCurvature r lam) (tailCurvatureSlope r lam)
    (tailCurvatureSecond r lam) (tailTau r lam) (tailLStar r lam) (tailEta r)
    (fun x _ => tail_curvature_derivative r lam x hl)
    (fun x _ => tail_curvature_second_derivative r lam x hl)
    (fun x hx => tail_second_derivative_lower r lam x hr h1 h2 hx) h8
    (tail_threshold_slope_lower r lam hr h1 h9) Y hY
  rw [tail_curvature_identity r lam Y hl, tail_curvature_identity r lam (tailTau r lam) hl,
    tail_probability_at_threshold r lam hl] at hdrop
  have hspos : 0 < tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact p_pos lam _ hl
  have hs1 : tailPStar r lam < 1 := by change 0 < 1 / 6 - tailPStar r lam at h1; linarith only [h1]
  have hv := (tailV_bounds (tailPStar r lam) hspos.le hs1.le).1
  have hP : 0 ≤ tailP1 r lam (tailPStar r lam) := by
    unfold tailP1
    have hv0 : 0 ≤ tailV (tailPStar r lam) := by linarith only [hv, hs1]
    positivity
  have hm := mul_le_mul_of_nonneg_right (tail_threshold_bounds r lam hr).2 hP
  unfold tailD
  linarith only [hdrop, hm]

end F4Heavy.Analysis
