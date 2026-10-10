module

public import F4Heavy.Analysis.TailGuardDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_source_derivative (r : Row) (lam Y : ℝ) (hl : 0 < lam) (hY : Y ≠ 0) :
    HasDerivAt (fun x => (tailK r lam * p lam x - tailP1 r lam (p lam x)) / x)
      ((tailP1 r lam (p lam Y) - tailK r lam * p lam Y -
        Y * p lam Y * (1 - p lam Y) *
          (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 + tailK r lam)) / Y ^ 2) Y := by
  convert (((tail_parent_probability_derivative lam Y hl).const_mul (tailK r lam)).sub
    (tail_p1_derivative r lam Y hl)).div (hasDerivAt_id Y) hY using 1
  · rfl
  · dsimp
    ring

theorem tail_source_derivative_numerator_bound (r : Row) (lam Y : ℝ)
    (hr : InRow r lam) (hY : 0 ≤ Y) (hpstar : p lam Y ≤ tailPStar r lam)
    (hmass : p lam Y * Y ≤ tailPStar r lam * tailTauHi r lam) :
    tailGuard r lam 7 ≤ tailP1 r lam (p lam Y) - tailK r lam * p lam Y -
      Y * p lam Y * (1 - p lam Y) *
        (1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 + tailK r lam) := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hp1 := p_lt_one lam Y hl
  have hg := row_gamma_pos r lam hr
  have hk : 0 < tailK r lam := by have hs := tailS_positive r lam hl; unfold tailK; positivity
  have hlin := tail_p1_order r lam (p lam Y) (tailPStar r lam) hg.le hp.le hpstar
  have hkp := mul_le_mul_of_nonneg_left hpstar hk.le
  have hcoef : 1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 + tailK r lam ≤
      tailAStar r lam + tailK r lam := by
    unfold tailAStar
    have h := mul_le_mul_of_nonneg_left hpstar hg.le
    linarith only [h]
  have hcoef0 : 0 ≤ 1 + gamma r lam / 2 + gamma r lam * p lam Y / 6 + tailK r lam := by positivity
  have hcoef1 : 0 ≤ tailAStar r lam + tailK r lam := hcoef0.trans hcoef
  have hweight0 : 0 ≤ Y * p lam Y * (1 - p lam Y) := by positivity
  have hweight : Y * p lam Y * (1 - p lam Y) ≤ tailPStar r lam * tailTauHi r lam := by
    have h := mul_le_mul_of_nonneg_left (show 1 - p lam Y ≤ 1 by linarith only [hp])
      (mul_nonneg hY hp.le)
    nlinarith only [h, hmass]
  have hprod := (mul_le_mul_of_nonneg_left hcoef hweight0).trans
    (mul_le_mul_of_nonneg_right hweight hcoef1)
  change tailP1 r lam (tailPStar r lam) - tailK r lam * tailPStar r lam -
    tailPStar r lam * tailTauHi r lam * (tailAStar r lam + tailK r lam) ≤ _
  linarith only [hlin, hkp, hprod]

theorem tail_source_monotone_of_guards (r : Row) (lam : ℝ) (hr : InRow r lam)
    (h1 : 0 < tailGuard r lam 1) (h2 : 0 < tailGuard r lam 2)
    (h7 : 0 < tailGuard r lam 7) :
    MonotoneOn (fun Y => (tailK r lam * p lam Y - tailP1 r lam (p lam Y)) / Y)
      (Set.Ici (tailTau r lam)) := by
  have hl := inRow_activity_pos r lam hr
  have ht := tail_threshold_lower_of_guard r lam hr h2
  have hpos : ∀ Y ∈ Set.Ici (tailTau r lam), 0 < Y := by
    intro Y hY
    have h := hY
    change tailTau r lam ≤ Y at h
    linarith only [ht, h]
  apply monotoneOn_of_deriv_nonneg (convex_Ici (tailTau r lam))
  · intro Y hY
    exact (tail_source_derivative r lam Y hl (hpos Y hY).ne').continuousAt.continuousWithinAt
  · intro Y hY
    exact (tail_source_derivative r lam Y hl (hpos Y (interior_subset hY)).ne').differentiableAt.differentiableWithinAt
  · intro Y hY
    have htY : tailTau r lam ≤ Y := interior_subset hY
    have hpstar : p lam Y ≤ tailPStar r lam := by
      rw [← tail_probability_at_threshold r lam hl]
      exact tail_probability_antitone lam (tailTau r lam) Y hl htY
    have hb := tail_source_derivative_numerator_bound r lam Y hr (hpos Y htY).le hpstar
      (tail_probability_mass_bound_of_guards r lam Y hr h1 h2 htY)
    rw [(tail_source_derivative r lam Y hl (hpos Y htY).ne').deriv]
    exact div_nonneg (h7.le.trans hb) (sq_nonneg Y)

theorem tail_source_lower_of_guards (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) (h1 : 0 < tailGuard r lam 1)
    (h2 : 0 < tailGuard r lam 2) (h6 : 0 < tailGuard r lam 6)
    (h7 : 0 < tailGuard r lam 7) :
    tailA r lam ≤ (tailK r lam * p lam Y - tailP1 r lam (p lam Y)) / Y := by
  have hmono := tail_source_monotone_of_guards r lam hr h1 h2 h7
    (show tailTau r lam ∈ Set.Ici (tailTau r lam) from le_rfl) hY hY
  dsimp only at hmono
  rw [tail_probability_at_threshold r lam (inRow_activity_pos r lam hr)] at hmono
  apply le_trans _ hmono
  unfold tailA
  have htlo : 0 < tailTauLo r lam := by change 0 < tailTauLo r lam - 3 / 2 at h2; linarith only [h2]
  have ht := (tail_threshold_bounds r lam hr).1
  have hnum : tailK r lam * tailPStar r lam - tailP1 r lam (tailPStar r lam) ≤ 0 := by
    change 0 < tailP1 r lam (tailPStar r lam) - tailK r lam * tailPStar r lam at h6
    linarith only [h6]
  apply (div_le_div_iff₀ htlo (htlo.trans_le ht)).mpr
  nlinarith only [mul_nonpos_of_nonpos_of_nonneg hnum (sub_nonneg.mpr ht)]

theorem tail_linear_lower (r : Row) (lam Y : ℝ) (hr : InRow r lam)
    (hY : tailTau r lam ≤ Y) :
    tailC r lam ≤ 2 * tailP1 r lam (p lam Y) - alpha r lam - beta r lam := by
  have hl := inRow_activity_pos r lam hr
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact tail_probability_antitone lam (tailTau r lam) Y hl hY
  have h := tail_p1_order r lam (p lam Y) (tailPStar r lam) (row_gamma_pos r lam hr).le
    (p_pos lam Y hl).le hpstar
  unfold tailC
  linarith only [h]

end F4Heavy.Analysis

