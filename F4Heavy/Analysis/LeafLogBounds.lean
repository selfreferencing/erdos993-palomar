module

public import F4Heavy.Analysis.LogBounds

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis

theorem probability_log_third_order_lower (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    2 * (p / (2 - p) + (p / (2 - p)) ^ 3 / 3 + (p / (2 - p)) ^ 5 / 5) ≤ -Real.log (1 - p) := by
  have hd : 0 < 2 - p := by linarith
  have hv0 : 0 ≤ p / (2 - p) := (div_pos hp hd).le
  have hv1 : p / (2 - p) < 1 := (div_lt_one hd).2 (by linarith)
  have hid : (1 + p / (2 - p)) / (1 - p / (2 - p)) = 1 / (1 - p) := by
    field_simp
    ring_nf
    rw [show 2 - p * 2 = 2 * (1 - p) by ring, mul_inv_rev]
    ring
  have h := Real.sum_range_le_log_div hv0 hv1 3
  rw [hid, Real.log_div (by norm_num) (ne_of_gt (show 0 < 1 - p by linarith)), Real.log_one] at h
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem probability_log_ratio_quartic_upper (p : ℝ) (hp : 0 < p) (hp1 : p < 1) :
    p / (-Real.log (1 - p)) ≤ 1 - p/2 - p^2/12 - p^3/24 - 19*p^4/720 := by
  have hd : 0 < 2-p := by linarith
  have hp2 : p^2 ≤ 1 := pow_le_one₀ hp.le hp1.le
  have hp3 : p^3 ≤ 1 := pow_le_one₀ hp.le hp1.le
  have hp4 : p^4 ≤ 1 := pow_le_one₀ hp.le hp1.le
  have hV : 0 ≤ 1-p/2-p^2/12-p^3/24-19*p^4/720 := by nlinarith
  have hid : (1-p/2-p^2/12-p^3/24-19*p^4/720)*
      (2*(p/(2-p)+(p/(2-p))^3/3+(p/(2-p))^5/5))-p =
      p^6*(373+1771*(1-p)+659*(1-p)^2+437*(1-p)^3)/(5400*(2-p)^5) := by
    field_simp
    <;> ring
  have hrem : 0 ≤ p^6*(373+1771*(1-p)+659*(1-p)^2+437*(1-p)^3)/(5400*(2-p)^5) := by
    have hq : 0 < 1-p := by linarith
    positivity
  have hmul := mul_le_mul_of_nonneg_left (probability_log_third_order_lower p hp hp1) hV
  have hlog : 0 < -Real.log (1-p) := by
    have hl := Real.log_neg (show 0 < 1-p by linarith) (show 1-p < 1 by linarith)
    linarith
  apply (div_le_iff₀ hlog).2
  nlinarith only [hid, hrem, hmul]

end F4Heavy.Analysis
