module

public import F4Heavy.Analysis.TailChildConstant
public import F4Heavy.Analysis.CapChildSlope

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_child_height_threshold (lam : ℝ) (hl : 0 < lam) :
    tailChildH0 lam ≤ childH (q lam) := by
  have hq := q_pos lam hl
  have hq1 := q_lt_one lam hl
  have hp := phi_positive (q lam) hq hq1
  have hd : 0 < (q lam) ^ 2 - 12 * q lam + 12 := by nlinarith only [sq_nonneg (q lam), hq1]
  have hden : 0 < 6 * (1 - q lam) * (2 - q lam) := by
    have h1 : 0 < 1 - q lam := sub_pos.mpr hq1
    have h2 : 0 < 2 - q lam := by linarith only [hq1]
    positivity
  have hb := (le_div_iff₀ hden).mp (phi_rational_upper (q lam) hq.le hq1)
  simp only [tailChildH0, childH, if_neg (ne_of_gt hq)]
  apply (div_le_div_iff₀ hd hp).mpr
  nlinarith only [hb]

theorem tail_child_height_range (lam u : ℝ) (hl : 0 < lam)
    (hu : 0 ≤ u) (huq : u ≤ q lam) :
    tailChildH0 lam ≤ childH u ∧ childH u ≤ 1 := by
  have hq1 := q_lt_one lam hl
  have hinc := cap_childH_height_increment u (q lam) hu huq hq1
  have hlo := tail_child_height_threshold lam hl
  have hhi := childH_linear_upper u hu (huq.trans_lt hq1)
  constructor <;> linarith only [hinc, hlo, hhi, hu, huq]

theorem tail_child_log_line (lam u : ℝ) (hl : 0 < lam) (hu : 0 < u) :
    u * Real.log (lam / u) ≤ 2 * u + lam * Real.exp (-3) := by
  have hz : 0 < lam * Real.exp (-3) / u := by positivity
  have h := Real.log_le_sub_one_of_pos hz
  rw [Real.log_div (ne_of_gt (mul_pos hl (Real.exp_pos (-3)))) (ne_of_gt hu),
    Real.log_mul (ne_of_gt hl) (ne_of_gt (Real.exp_pos (-3))), Real.log_exp] at h
  have hm := mul_le_mul_of_nonneg_left h hu.le
  rw [Real.log_div (ne_of_gt hl) (ne_of_gt hu)]
  have hid : u * (lam * Real.exp (-3) / u - 1) = lam * Real.exp (-3) - u := by field_simp
  rw [hid] at hm
  linarith only [hm]

theorem tail_child_exponential_remainder (r : Row) (lam : ℝ) (hr : InRow r lam) :
    lam * Real.exp (-3) < 1 / 8 := by
  have hb := (cap_row_activity_bounds r lam hr).2
  have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num) 8
  norm_num [Finset.sum_range_succ] at he
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos 3)).mpr
  linarith only [hb, he]

theorem tail_childJ_line_upper (r : Row) (lam u : ℝ) (hr : InRow r lam)
    (hu : 0 ≤ u) (huq : u ≤ q lam) : childJ lam u ≤ 33 / 8 - 4 * childH u := by
  have hl := inRow_activity_pos r lam hr
  have hu1 := huq.trans_lt (q_lt_one lam hl)
  by_cases hz : u = 0
  · subst u
    norm_num [childJ, childH]
  have hup : 0 < u := lt_of_le_of_ne hu (Ne.symm hz)
  have harg : 1 ≤ lam * (1 - u) / u := by
    have h := (le_div_iff₀ (show 0 < 1 + lam by linarith)).mp huq
    apply (le_div_iff₀ hup).mpr
    nlinarith only [h]
  have hT := Real.log_nonneg harg
  have hH := childH_linear_upper u hu hu1
  have hH1 : childH u ≤ 1 := by linarith only [hH, hu]
  have hJ := mul_le_mul_of_nonneg_left hH1 (mul_nonneg hu hT)
  have hlog : Real.log (lam * (1 - u) / u) ≤ Real.log (lam / u) := by
    apply Real.log_le_log (div_pos (mul_pos hl (sub_pos.mpr hu1)) hup)
    apply div_le_div_of_nonneg_right _ hu
    nlinarith only [mul_nonneg hl.le hu]
  have hm := mul_le_mul_of_nonneg_left hlog hu
  have hline := tail_child_log_line lam u hl hup
  have hexp := tail_child_exponential_remainder r lam hr
  simp only [childJ, if_neg hz]
  nlinarith only [hJ, hm, hline, hexp, hH]

end F4Heavy.Analysis
