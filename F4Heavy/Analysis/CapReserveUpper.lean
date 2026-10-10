module

public import F4Heavy.Analysis.CapFieldBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_exponential_guard (lam : ℝ) (hl : 4 / 5 ≤ lam) (hu : lam ≤ 7 / 3) :
    0 < -12 * lam ^ 3 + 109 * lam ^ 2 + 264 * lam - 252 := by
  have h1 := mul_nonneg (sq_nonneg lam) (show 0 ≤ 7 / 3 - lam by linarith only [hu])
  have h2 := mul_nonneg (show 0 ≤ lam - 4 / 5 by linarith only [hl])
    (show 0 ≤ lam + 4 / 5 by linarith only [hl])
  nlinarith only [h1, h2, hl]

theorem cap_reserve_log_bound (lam : ℝ) (hl : 4 / 5 ≤ lam) (hu : lam ≤ 7 / 3) :
    Real.log (lam / (2 * lam / (6 + lam))) < 1 + 2 * lam / (6 + lam) := by
  have hlam : 0 < lam := by linarith only [hl]
  have hden : 0 < 6 + lam := by linarith only [hl]
  let B := 2 * lam / (6 + lam)
  have hB : 0 < B := div_pos (mul_pos (by norm_num) hlam) hden
  have he : (65 : ℝ) / 24 ≤ Real.exp 1 := by
    have hs := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num) 5
    norm_num [Finset.sum_range_succ] at hs
    exact hs
  have hquad := Real.quadratic_le_exp_of_nonneg hB.le
  have hprod := mul_le_mul he hquad (by positivity : 0 ≤ 1 + B + B ^ 2 / 2) (Real.exp_pos 1).le
  have hm := mul_le_mul_of_nonneg_left hprod hB.le
  have hid : B * ((65 / 24) * (1 + B + B ^ 2 / 2)) - lam =
      lam * (-12 * lam ^ 3 + 109 * lam ^ 2 + 264 * lam - 252) / (12 * (6 + lam) ^ 3) := by
    dsimp [B]
    field_simp
    <;> ring
  have hg : 0 < lam * (-12 * lam ^ 3 + 109 * lam ^ 2 + 264 * lam - 252) /
      (12 * (6 + lam) ^ 3) := div_pos (mul_pos hlam (cap_exponential_guard lam hl hu)) (by positivity)
  have hexp : lam < B * Real.exp (1 + B) := by
    rw [Real.exp_add]
    nlinarith only [hm, hid, hg]
  have hdiv : lam / B < Real.exp (1 + B) :=
    (div_lt_iff₀ hB).mpr (by nlinarith only [hexp])
  have hlog := Real.log_lt_log (div_pos hlam hB) hdiv
  rw [Real.log_exp] at hlog
  exact hlog

theorem cap_child_u_log_upper (lam u : ℝ) (hl : 4 / 5 ≤ lam) (hu : lam ≤ 7 / 3)
    (hu0 : 0 < u) (hu1 : u < 1) :
    u * Real.log (lam * (1 - u) / u) ≤ 2 * lam / (6 + lam) := by
  have hlam : 0 < lam := by linarith only [hl]
  let B := 2 * lam / (6 + lam)
  have hB : 0 < B := div_pos (mul_pos (by norm_num) hlam) (by linarith)
  have hz : 0 < B * (1 - u) / u := div_pos (mul_pos hB (sub_pos.mpr hu1)) hu0
  have hl1 := cap_reserve_log_bound lam hl hu
  change Real.log (lam / B) < 1 + B at hl1
  have hl2 := Real.log_le_sub_one_of_pos hz
  have hid : lam * (1 - u) / u = (lam / B) * (B * (1 - u) / u) := by
    field_simp
  rw [hid, Real.log_mul (ne_of_gt (div_pos hlam hB)) (ne_of_gt hz)]
  have hsum : Real.log (lam / B) + Real.log (B * (1 - u) / u) ≤
      B + B * (1 - u) / u := by linarith only [hl1, hl2]
  have hm := mul_le_mul_of_nonneg_left hsum hu0.le
  have hclear : u * (B + B * (1 - u) / u) = B := by
    field_simp
    <;> ring
  rw [hclear] at hm
  exact hm

theorem cap_childJ_reserve_upper (r : Row) (lam Y u : ℝ) (hr : InRow r lam)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) :
    childJ lam u ≤ (2 * lam / (6 + lam)) * childH u := by
  have hl := inRow_activity_pos r lam hr
  have bounds := cap_row_activity_bounds r lam hr
  have hu1 := huc.trans_lt (cap_child_lt_one lam Y hl)
  have hh := (cap_child_height_bounds lam Y u hl hu huc).1
  have h := mul_le_mul_of_nonneg_right
    (cap_child_u_log_upper lam u bounds.1 bounds.2 hu hu1) hh.le
  simp only [childJ, if_neg (ne_of_gt hu)]
  convert h using 1 <;> ring

end F4Heavy.Analysis
