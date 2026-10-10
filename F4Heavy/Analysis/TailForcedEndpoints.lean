module

public import F4Heavy.Analysis.TailModelPositive

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_zero_forced_positive_of_bounds (r : Row) (lam Y u : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hpstar : p lam Y ≤ tailPStar r lam)
    (hpY : p lam Y * Y ≤ tailPStar r lam * tailTauHi r lam)
    (h3 : 0 < tailGuard r lam 3) (h4 : 0 < tailGuard r lam 4)
    (h5 : 0 < tailGuard r lam 5) : 0 < tailEndpointZero r lam Y u (childH u) := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hg := row_gamma_pos r lam hr
  have hv := tailV_bounds (p lam Y) hp.le (p_lt_one lam Y hl).le
  have hq := tail_zero_quadratic_positive (alpha r lam) (gamma r lam)
    (alpha r lam + beta r lam) (tailS r lam) (p lam Y) (tailPStar r lam) Y
    (tailTauHi r lam) (tailV (p lam Y)) (tailD0 r lam) hp hpstar hY hpY hg.le
    (tailS_positive r lam hl).le hv.1 hv.2 (by simpa [tailGuard] using h3)
    h4 (by simpa [tailGuard, tailM0, tailC0] using h5) (childH u)
  have hweight : 0 ≤ tailPStar r lam * tailTauHi r lam - p lam Y * Y * tailV (p lam Y) := by
    have h := mul_le_mul_of_nonneg_left hv.2 (mul_pos hp hY).le
    linarith only [h, hpY]
  have hcurv : tailD0 r lam / p lam Y ≤
      (gamma r lam - delta r lam) / p lam Y - Y * gamma r lam * tailV (p lam Y) := by
    have hm := mul_nonneg hg.le hweight
    apply (div_le_iff₀ hp).mpr
    have hid : ((gamma r lam - delta r lam) / p lam Y - Y * gamma r lam * tailV (p lam Y)) * p lam Y =
        gamma r lam - delta r lam - gamma r lam * (p lam Y * Y * tailV (p lam Y)) := by field_simp
    rw [hid]
    unfold tailD0
    nlinarith only [hm]
  have hc := mul_le_mul_of_nonneg_right hcurv (sq_nonneg (childH u))
  unfold tailEndpointZero responsePolynomial
  simp only [zero_mul, add_zero, sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  nlinarith only [hq, hc]

theorem tail_zero_forced_positive_of_guards (r : Row) (lam Y u : ℝ)
    (hr : InRow r lam) (hY : tailTau r lam ≤ Y)
    (hguards : ∀ i, 1 ≤ i → i ≤ 5 → 0 < tailGuard r lam i) :
    0 < tailEndpointZero r lam Y u (childH u) := by
  have hl := inRow_activity_pos r lam hr
  have ht := tail_threshold_lower_of_guard r lam hr (hguards 2 (by omega) (by omega))
  have hpstar : p lam Y ≤ tailPStar r lam := by
    rw [← tail_probability_at_threshold r lam hl]
    exact tail_probability_antitone lam (tailTau r lam) Y hl hY
  exact tail_zero_forced_positive_of_bounds r lam Y u hr (by linarith only [ht, hY]) hpstar
    (tail_probability_mass_bound_of_guards r lam Y hr (hguards 1 (by omega) (by omega))
      (hguards 2 (by omega) (by omega)) hY)
    (hguards 3 (by omega) (by omega)) (hguards 4 (by omega) (by omega))
    (hguards 5 (by omega) (by omega))

theorem tail_one_forced_positive_of_guards (r : Row) (lam Y u : ℝ)
    (hr : InRow r lam) (hY : tailTau r lam ≤ Y) (hu : 0 ≤ u) (huq : u ≤ q lam)
    (hguards : ∀ i, 1 ≤ i → i ≤ 16 → 0 < tailGuard r lam i) :
    0 < tailEndpointOne r lam Y u (childH u) := by
  have hl := inRow_activity_pos r lam hr
  have hh := tail_child_height_range lam u hl hu huq
  have hh0 := childH_nonnegative u hu (huq.trans_lt (q_lt_one lam hl))
  have hC := tail_childC_range r lam hr
  have hmodel := tail_model_positive_of_guards r lam (1 / 8) (childH u) (childH u) hr
    (by norm_num) (by linarith only [hC.1]) (by linarith only [hh.2]) hh.1 hh.2
    (hguards 12 (by omega) (by omega)) (hguards 13 (by omega) (by omega))
    (hguards 14 (by omega) (by omega)) (hguards 15 (by omega) (by omega))
    (hguards 16 (by omega) (by omega))
  have ha := tail_source_lower_of_guards r lam Y hr hY
    (hguards 1 (by omega) (by omega)) (hguards 2 (by omega) (by omega))
    (hguards 6 (by omega) (by omega)) (hguards 7 (by omega) (by omega))
  have hc := mul_le_mul_of_nonneg_right (tail_linear_lower r lam Y hr hY) hh0
  have hd := mul_le_mul_of_nonneg_right (tail_curvature_lower_of_guards r lam Y hr hY
    (hguards 1 (by omega) (by omega)) (hguards 2 (by omega) (by omega))
    (hguards 8 (by omega) (by omega)) (hguards 9 (by omega) (by omega))) (sq_nonneg (childH u))
  dsimp only [tailModel, tailEndpointOne, responsePolynomial] at hmodel ⊢
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hmodel ⊢
  linarith only [hmodel, ha, hc, hd]

theorem tail_forced_mixture_identity (r : Row) (lam Y rho u : ℝ)
    (hl : 0 < lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1) :
    paymentWithParent r lam Y rho u (childH u)
        (rho * (1 - p lam Y) + gamma r lam * tailV (p lam Y)) / p lam Y -
      ((1 - rho) * tailEndpointZero r lam Y u (childH u) +
        rho * tailEndpointOne r lam Y u (childH u)) =
        tailS r lam * p lam Y / Y * (rho - 1 / 2) ^ 2 := by
  have hp := p_pos lam Y hl
  unfold paymentWithParent
  rw [heavy_source_term r lam Y rho hl hrho hx]
  unfold tailEndpointZero tailEndpointOne responsePolynomial tailP1 tailK reserve
  simp only [sub_self, zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_div, ite_self, add_zero]
  have hk : heavyK r lam Y = tailS r lam * p lam Y := rfl
  rw [hk]
  field_simp
  <;> ring

theorem tail_forced_payment_positive (r : Row) (lam Y rho u : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hrho : FeasibleVacancy lam Y rho)
    (hx : parentX lam Y ≤ 1)
    (hzero : 0 < tailEndpointZero r lam Y u (childH u))
    (hone : 0 < tailEndpointOne r lam Y u (childH u)) :
    0 < payment r lam Y rho u (childH u) := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hv := feasible_vacancy_pos lam Y rho hl hrho
  have hmix := add_pos_of_nonneg_of_pos
    (mul_nonneg (sub_nonneg.mpr hrho.2) hzero.le) (mul_pos hv hone)
  have hreplace := parent_replacement_lower_bound r lam Y rho u (childH u)
    (rho * (1 - p lam Y) + gamma r lam * tailV (p lam Y)) hp.le hY
    (parentP_quadratic_upper r lam Y rho hr)
  have hdiv := div_le_div_of_nonneg_right hreplace hp.le
  have hid := tail_forced_mixture_identity r lam Y rho u hl hY hrho hx
  have hnon := mul_nonneg (div_nonneg (mul_nonneg (tailS_positive r lam hl).le hp.le) hY.le)
    (sq_nonneg (rho - 1 / 2))
  have hpos : 0 < payment r lam Y rho u (childH u) / p lam Y := by linarith only [hmix, hdiv, hid, hnon]
  exact (div_pos_iff_of_pos_right hp).mp hpos

end F4Heavy.Analysis
