module

public import F4Heavy.Analysis.Quadratic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

-- Analytic bounds, proved from Mathlib's real logarithm series, not assumed
-- from the finite JSON arithmetic. The 16-term bound below has ample slack
-- for the fixed 12-decimal upper constant used by the original certificates.
theorem log_four_lt_certificate_constant : Real.log 4 < (1386294361120 : ℝ) / 1000000000000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 16
  norm_num [Finset.sum_range_succ] at h
  have h4 := Real.log_mul (show (2 : ℝ) ≠ 0 by norm_num) (show (2 : ℝ) ≠ 0 by norm_num)
  norm_num at h4
  linarith

theorem negative_log_lower_bound (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    2 * (1 - x) / (1 + x) ≤ -Real.log x := by
  let v := (1 - x) / (1 + x)
  have hd : 0 < 1 + x := by linarith
  have hv0 : 0 ≤ v := div_nonneg (by linarith) hd.le
  have hv1 : v < 1 := (div_lt_one hd).2 (by linarith)
  have hid : (1 + v) / (1 - v) = 1 / x := by
    dsimp [v]
    field_simp
    ring_nf
    simp [ne_of_gt hx]
  have h := Real.sum_range_le_log_div hv0 hv1 1
  rw [hid, Real.log_div (by norm_num) (ne_of_gt hx), Real.log_one] at h
  norm_num [Finset.sum_range_succ] at h
  dsimp [v] at h
  rw [mul_div_assoc]
  linarith

theorem probability_log_ratio_linear_upper (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p / (-Real.log (1 - p)) ≤ 1 - p / 2 := by
  have hd : 0 < 2 - p := by linarith
  have hb : 2 * p / (2 - p) ≤ -Real.log (1 - p) := by
    convert negative_log_lower_bound (1 - p) (by linarith) (by linarith) using 1 <;> ring
  have hlog : 0 < -Real.log (1 - p) := lt_of_lt_of_le (div_pos (by positivity) hd) hb
  have hprod := (div_le_iff₀ hd).mp hb
  apply (div_le_iff₀ hlog).2
  nlinarith

theorem probability_log_second_order_lower (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    2 * (p / (2 - p) + (p / (2 - p)) ^ 3 / 3) ≤ -Real.log (1 - p) := by
  have hd : 0 < 2 - p := by linarith
  have hv0 : 0 ≤ p / (2 - p) := (div_pos hp hd).le
  have hv1 : p / (2 - p) < 1 := (div_lt_one hd).2 (by linarith)
  have hid : (1 + p / (2 - p)) / (1 - p / (2 - p)) = 1 / (1 - p) := by
    field_simp
    ring_nf
    rw [show 2 - p * 2 = 2 * (1 - p) by ring, mul_inv_rev]
    ring
  have h := Real.sum_range_le_log_div hv0 hv1 2
  rw [hid, Real.log_div (by norm_num) (ne_of_gt (show 0 < 1 - p by linarith)), Real.log_one] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem probability_log_ratio_quadratic_upper (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p / (-Real.log (1 - p)) ≤ 1 - p / 2 - p ^ 2 / 12 := by
  have hd : 0 < 2 - p := by linarith
  have hV : 0 ≤ 1 - p / 2 - p ^ 2 / 12 := by nlinarith [sq_nonneg (1 - p)]
  have hid : (1 - p / 2 - p ^ 2 / 12) *
      (2 * (p / (2 - p) + (p / (2 - p)) ^ 3 / 3)) - p =
      p ^ 4 * (3 - 2 * p) / (9 * (2 - p) ^ 3) := by
    field_simp
    <;> ring
  have hfactor : 0 < 3 - 2 * p := by linarith
  have hrem : 0 ≤ p ^ 4 * (3 - 2 * p) / (9 * (2 - p) ^ 3) := by positivity
  have hbound := probability_log_second_order_lower p hp hp1
  have hmul := mul_le_mul_of_nonneg_left hbound hV
  have hlog : 0 < -Real.log (1 - p) := by
    have hl := Real.log_neg (show 0 < 1 - p by linarith) (show 1 - p < 1 by linarith)
    linarith
  apply (div_le_iff₀ hlog).2
  nlinarith only [hid, hrem, hmul]

end F4Heavy.Analysis
