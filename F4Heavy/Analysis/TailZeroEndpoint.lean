module

public import F4Heavy.Analysis.TailSource

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tailV_bounds (x : ℝ) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 - x ≤ tailV x ∧ tailV x ≤ 1 := by
  unfold tailV
  have h := mul_nonneg hx (sub_nonneg.mpr hx1)
  constructor <;> nlinarith only [h, hx, sq_nonneg x]

theorem tail_zero_quadratic_positive (a g A S p ps Y t V d : ℝ)
    (hp : 0 < p) (hps : p ≤ ps) (hY : 0 < Y) (hpt : p * Y ≤ ps * t)
    (hg : 0 ≤ g) (hS : 0 ≤ S) (hV : 1 - p ≤ V) (hV1 : V ≤ 1)
    (hA : 2 * g < A) (hd : 0 < d)
    (hdisc : ps * t * (A - 2 * g * (1 - ps)) ^ 2 < 4 * d * (a - g - S * ps / 4))
    (y : ℝ) :
    0 < (a - g * V - S * p / 4) / Y + (2 * g * V - A) * y + (d / p) * y ^ 2 := by
  have hVlo : 1 - ps ≤ V := by linarith only [hps, hV]
  have hmul := mul_le_mul_of_nonneg_left hVlo (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg)
  have hmul1 := mul_le_mul_of_nonneg_left hV1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hg)
  have hsq : (2 * g * V - A) ^ 2 ≤ (A - 2 * g * (1 - ps)) ^ 2 := by
    nlinarith only [hmul, hmul1, hA,
      mul_nonneg (show 0 ≤ (A - 2 * g * (1 - ps)) - (A - 2 * g * V) by linarith only [hmul])
        (show 0 ≤ (A - 2 * g * (1 - ps)) + (A - 2 * g * V) by linarith only [hmul, hmul1, hA])]
  have hsource : a - g - S * ps / 4 ≤ a - g * V - S * p / 4 := by
    have hv := mul_le_mul_of_nonneg_left hV1 hg
    have hs := mul_le_mul_of_nonneg_left hps hS
    linarith only [hv, hs]
  have hprod := mul_le_mul_of_nonneg_right hpt (sq_nonneg (A - 2 * g * (1 - ps)))
  have hsmall := mul_le_mul_of_nonneg_left hsq (mul_pos hp hY).le
  have hm := mul_le_mul_of_nonneg_left hsource (mul_pos (by norm_num : (0 : ℝ) < 4) hd).le
  have hnum : 0 < 4 * d * (a - g * V - S * p / 4) - p * Y * (2 * g * V - A) ^ 2 := by
    linarith only [hdisc, hprod, hsmall, hm]
  have hid : 4 * (d / p) * ((a - g * V - S * p / 4) / Y) - (2 * g * V - A) ^ 2 =
      (4 * d * (a - g * V - S * p / 4) - p * Y * (2 * g * V - A) ^ 2) / (p * Y) := by
    field_simp
    <;> ring
  have hq := quadratic_positive (d / p) (2 * g * V - A) ((a - g * V - S * p / 4) / Y) y
    (div_pos hd hp) (by rw [hid]; exact div_pos hnum (mul_pos hp hY))
  linarith only [hq]

theorem tail_zero_endpoint_positive_of_bounds (r : Row) (lam Y u y : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hpstar : p lam Y ≤ tailPStar r lam)
    (hpY : p lam Y * Y ≤ tailPStar r lam * tailTauHi r lam)
    (h3 : 0 < tailGuard r lam 3) (h4 : 0 < tailGuard r lam 4)
    (h5 : 0 < tailGuard r lam 5) (hJ : 0 < childJ lam u) :
    0 < tailEndpointZero r lam Y u y := by
  have hl := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hl
  have hg := row_gamma_pos r lam hr
  have hv := tailV_bounds (p lam Y) hp.le (p_lt_one lam Y hl).le
  have hq := tail_zero_quadratic_positive (alpha r lam) (gamma r lam)
    (alpha r lam + beta r lam) (tailS r lam) (p lam Y) (tailPStar r lam) Y
    (tailTauHi r lam) (tailV (p lam Y)) (tailD0 r lam) hp hpstar hY hpY hg.le
    (tailS_positive r lam hl).le hv.1 hv.2 (by simpa [tailGuard] using h3)
    h4 (by simpa [tailGuard, tailM0, tailC0] using h5) y
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
  have hc := mul_le_mul_of_nonneg_right hcurv (sq_nonneg y)
  have hres := mul_nonneg (div_nonneg (div_pos (row_delta_pos r lam hr) hp).le hJ.le) (sq_nonneg (childH u - y))
  unfold tailEndpointZero responsePolynomial
  simp only [zero_mul, add_zero]
  nlinarith only [hq, hc, hres]

end F4Heavy.Analysis
