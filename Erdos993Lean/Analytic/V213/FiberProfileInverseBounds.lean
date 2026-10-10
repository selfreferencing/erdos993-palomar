module

public import Erdos993Lean.Analytic.V213.FiberProfileInverse
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Printed inverse-root thresholds and the log-test-to-tangent-slope
bridge. Both thresholds follow actual fifth powers of T and the proved
analytic exponential constant; no numerical root approximation is used.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

theorem fiber_exp_one_upper : Real.exp 1 < 11 / 4 := by
  linarith only [Real.exp_one_lt_d9]

theorem fiber_profile_T_fifth {a : ℝ} (ha : a < 1) :
    (fiberProfileT a) ^ 5 = Real.exp (-2 * a) * (1 - a) ^ 2 := by
  have hd : 0 < 1 - a := by linarith only [ha]
  unfold fiberProfileT
  rw [← Real.exp_nat_mul]
  norm_num
  have hid : 5 * ((2 / 5 : ℝ) * (-a + Real.log (1 - a))) =
      -2 * a + 2 * Real.log (1 - a) := by ring
  rw [hid,Real.exp_add]
  have he : Real.exp (2 * Real.log (1 - a)) = (1 - a) ^ 2 := by
    simpa only [Nat.cast_ofNat,Real.exp_log hd] using (Real.exp_nat_mul (Real.log (1 - a)) 2)
  rw [he]
  simp only [neg_mul]

theorem fiber_profile_T_half : (3 / 5 : ℝ) < fiberProfileT (1 / 2) := by
  have he := fiber_exp_one_upper
  have hep := Real.exp_pos (1 : ℝ)
  have ht := fiber_profile_T_fifth (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at ht
  rw [Real.exp_neg] at ht
  have hpow : (3 / 5 : ℝ) ^ 5 < (fiberProfileT (1 / 2)) ^ 5 := by
    rw [ht]
    have hrec : (1 / 11 : ℝ) < (Real.exp 1)⁻¹ * (1 / 4) := by
      rw [inv_eq_one_div]
      have h : (1 / 11 : ℝ) < (1 / 4) / Real.exp 1 := by
        apply (lt_div_iff₀ hep).2
        linarith only [he]
      convert h using 1 <;> ring
    exact (by norm_num : (3 / 5 : ℝ) ^ 5 < 1 / 11).trans hrec
  exact lt_of_pow_lt_pow_left₀ 5 (fiber_profile_T_positive _).le hpow

theorem fiber_profile_T_three_quarters : (19 / 50 : ℝ) < fiberProfileT (3 / 4) := by
  have he := fiber_exp_one_upper
  have hep := Real.exp_pos (1 : ℝ)
  have ht := fiber_profile_T_fifth (by norm_num : (3 / 4 : ℝ) < 1)
  norm_num at ht
  have hexp : Real.exp (-(2 : ℝ)) < Real.exp (-(3 / 2 : ℝ)) := Real.exp_lt_exp.mpr (by norm_num)
  have hrec : (1 / 121 : ℝ) < Real.exp (-2) * (1 / 16) := by
    have he2 : (Real.exp 1) ^ 2 < (121 / 16 : ℝ) := by nlinarith only [he,hep]
    have heq : Real.exp (-2) = ((Real.exp 1) ^ 2)⁻¹ := by
      rw [show -(2 : ℝ) = -(2 * 1) by ring,Real.exp_neg]
      have hpow : Real.exp (2 * 1) = (Real.exp 1) ^ 2 := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul (1 : ℝ) 2)
      rw [hpow]
    rw [heq,inv_eq_one_div]
    have hd : 0 < (Real.exp 1) ^ 2 := sq_pos_of_pos hep
    have h : (1 / 121 : ℝ) * ((Real.exp 1) ^ 2) < 1 / 16 := by linarith only [he2]
    convert (lt_div_iff₀ hd).2 h using 1 <;> ring
  have hpow : (19 / 50 : ℝ) ^ 5 < (fiberProfileT (3 / 4)) ^ 5 := by
    rw [ht]
    have hstep := mul_lt_mul_of_pos_right hexp (by norm_num : (0 : ℝ) < 1 / 16)
    exact (by norm_num : (19 / 50 : ℝ) ^ 5 < 1 / 121).trans (hrec.trans hstep)
  exact lt_of_pow_lt_pow_left₀ 5 (fiber_profile_T_positive _).le hpow

theorem fiber_profile_actual_root_half {t : ℝ} (ht : 0 < t) (hth : t ≤ 3 / 5) :
    1 / 2 < fiberRayAroot t := by
  have ht1 : t < 1 := by linarith only [hth]
  have ha1 := (fiber_ray_root_formulas ht ht1).2.1
  by_contra hn
  have ha : fiberRayAroot t ≤ 1 / 2 := le_of_not_gt hn
  have hm := fiber_profile_T_decreases.antitoneOn ha1 (by norm_num) ha
  rw [fiber_profile_T_actual ht ht1] at hm
  linarith only [hm,hth,fiber_profile_T_half]

theorem fiber_profile_actual_root_three_quarters {t : ℝ} (ht : 0 < t) (hth : t ≤ 19 / 50) :
    3 / 4 < fiberRayAroot t := by
  have ht1 : t < 1 := by linarith only [hth]
  have ha1 := (fiber_ray_root_formulas ht ht1).2.1
  by_contra hn
  have ha : fiberRayAroot t ≤ 3 / 4 := le_of_not_gt hn
  have hm := fiber_profile_T_decreases.antitoneOn ha1 (by norm_num) ha
  rw [fiber_profile_T_actual ht ht1] at hm
  linarith only [hm,hth,fiber_profile_T_three_quarters]

theorem fiber_profile_root_slope_from_log {v beta : ℝ} (hv : v < 1) (hbeta : 0 < beta)
    (hlog : Real.log ((1 - v) ^ 2 * (beta / fiberProfileTangentK v) ^ 5) < 2 * v) :
    beta < fiberProfileTangentK v / fiberProfileT v := by
  have hk := (fiber_profile_tangent_K hv).1
  have hd : 0 < 1 - v := by linarith only [hv]
  have hy : 0 < (1 - v) ^ 2 * (beta / fiberProfileTangentK v) ^ 5 := by positivity
  have he := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log hy] at he
  have hmul := mul_lt_mul_of_pos_right he (Real.exp_pos (-2 * v))
  have hcancel : Real.exp (2 * v) * Real.exp (-2 * v) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hmul
  have hid : (1 - v) ^ 2 * (beta / fiberProfileTangentK v) ^ 5 * Real.exp (-2 * v) =
      (beta * fiberProfileT v) ^ 5 / (fiberProfileTangentK v) ^ 5 := by
    rw [mul_pow,div_pow,fiber_profile_T_fifth hv]
    ring
  rw [hid] at hmul
  have hp := (div_lt_one (pow_pos hk 5)).mp hmul
  have hbase := lt_of_pow_lt_pow_left₀ 5 hk.le hp
  exact (lt_div_iff₀ (fiber_profile_T_positive _)).2 hbase

end Erdos993Lean.Analytic.V213
