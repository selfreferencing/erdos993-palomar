module

public import F4Heavy.Analysis.DHAllSupports

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem activity_transform_bounds (a b lam : ℝ) (ha : 0 < a) (hab : a < b)
    (hl : a ≤ lam) (hu : lam ≤ b) :
    0 ≤ (lam-a)/(lam+a) ∧ (lam-a)/(lam+a) ≤ (b-a)/(b+a) ∧
      (b-a)/(b+a) < 1 := by
  have hd : 0 < lam+a := by linarith
  have hb : 0 < b+a := by linarith
  refine ⟨div_nonneg (sub_nonneg.mpr hl) hd.le, ?_, ?_⟩
  · apply (div_le_div_iff₀ hd hb).mpr
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hu)]
  · exact (div_lt_one hb).mpr (by linarith only [ha])

theorem rational_log_upper_mono (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v < 1) :
    2*u+2*u^3/(3*(1-u^2)) ≤ 2*v+2*v^3/(3*(1-v^2)) := by
  have hv0 := hu.trans huv
  have h2 := pow_le_pow_left₀ hu huv 2
  have h3 := pow_le_pow_left₀ hu huv 3
  have hd : 0 < 3*(1-v^2) := by nlinarith only [hv, hv0, sq_nonneg (1-v)]
  have hdiv : 2*u^3/(3*(1-u^2)) ≤ 2*v^3/(3*(1-v^2)) :=
    div_le_div₀ (by positivity) (by linarith only [h3]) hd (by linarith only [h2])
  linarith only [hdiv, huv]

theorem rational_activity_weight_bounds (a b lam ell : ℝ) (ha : 0 < a) (hab : a < b)
    (hl : a ≤ lam) (hu : lam ≤ b) (hell : 0 < ell) :
    let v := (lam-a)/(lam+a)
    let t := (b-a)/(b+a)
    0 ≤ (2*v+2*v^3/(3*(1-v^2)))/ell ∧
      (2*v+2*v^3/(3*(1-v^2)))/ell ≤ (2*t+2*t^3/(3*(1-t^2)))/ell := by
  have h := activity_transform_bounds a b lam ha hab hl hu
  have hv1 := lt_of_le_of_lt h.2.1 h.2.2
  have hd : 0 < 3*(1-((lam-a)/(lam+a))^2) := by
    nlinarith only [hv1, h.1, sq_nonneg (1-(lam-a)/(lam+a))]
  refine ⟨div_nonneg (add_nonneg (mul_nonneg (by norm_num) h.1)
    (div_nonneg (mul_nonneg (by norm_num) (pow_nonneg h.1 3)) hd.le)) hell.le, ?_⟩
  exact div_le_div_of_nonneg_right (rational_log_upper_mono _ _ h.1 h.2.1 h.2.2) hell.le

end F4Heavy.Analysis
