module

public import Erdos993Lean.Analytic.V213.FiberWindowInverseDefinitions

/-!
Both printed inverse inequalities hold for every x>0. The separate
5/9 cap is restricted to x<=1. The radical is an actual positive quadratic
root, and its exponential cost is bounded by the elementary comparison.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_window_radical_form {x : ℝ} (hx : 0 < x) :
    fiberWindowInverseRadical x = (Real.sqrt (4 + 12 * x + x ^ 2) - 2 - x) / 2 := by
  have hd : 0 < Real.sqrt (4 + 12 * x + x ^ 2) + 2 + x := by positivity
  have hs := Real.sq_sqrt (show 0 ≤ 4 + 12 * x + x ^ 2 by positivity)
  unfold fiberWindowInverseRadical
  apply (div_eq_iff hd.ne').2
  nlinarith only [hs]

theorem fiber_window_radical_domain {x : ℝ} (hx : 0 < x) :
    0 < fiberWindowInverseRadical x ∧ fiberWindowInverseRadical x < 2 := by
  have hp : 0 < fiberWindowInverseRadical x := by unfold fiberWindowInverseRadical; positivity
  have hs := Real.sq_sqrt (show 0 ≤ 4 + 12 * x + x ^ 2 by positivity)
  have hs0 := Real.sqrt_nonneg (4 + 12 * x + x ^ 2)
  have hl : Real.sqrt (4 + 12 * x + x ^ 2) < x + 6 := by nlinarith only [hs,hs0,hx]
  rw [fiber_window_radical_form hx]
  constructor
  · rwa [fiber_window_radical_form hx] at hp
  · linarith only [hl]

theorem fiber_window_radical_quadratic {x : ℝ} (hx : 0 < x) :
    (fiberWindowInverseRadical x) ^ 2 + (2 + x) * fiberWindowInverseRadical x - 2 * x = 0 := by
  rw [fiber_window_radical_form hx]
  have hs := Real.sq_sqrt (show 0 ≤ 4 + 12 * x + x ^ 2 by positivity)
  nlinarith only [hs]

theorem fiber_window_radical_cost {x : ℝ} (hx : 0 < x) :
    fiberWindowInverseRadical x * Real.exp (fiberWindowInverseRadical x) ≤ x := by
  have hd := fiber_window_radical_domain hx
  have he := fiber_window_radical_quadratic hx
  have hp := mul_le_mul_of_nonneg_left (fiber_exp_pade_upper hd.1.le hd.2) hd.1.le
  have hratio : fiberWindowInverseRadical x *
      ((2 + fiberWindowInverseRadical x) / (2 - fiberWindowInverseRadical x)) = x := by
    rw [← mul_div_assoc]
    apply (div_eq_iff (ne_of_gt (by linarith : 0 < 2 - fiberWindowInverseRadical x))).2
    nlinarith only [he]
  rwa [hratio] at hp

theorem fiber_window_inverse_quadratic {x : ℝ} (hx : 0 ≤ x) :
    (fiberWindowInverse x) ^ 2 + (2 + x) * fiberWindowInverse x - 2 * x =
      -2 * x ^ 5 / (2 + 5 * x + 2 * x ^ 2) ^ 2 := by
  have hd : 0 < 2 + 5 * x + 2 * x ^ 2 := by positivity
  unfold fiberWindowInverse
  field_simp [hd.ne'] <;> ring

theorem fiber_window_inverse_le_radical {x : ℝ} (hx : 0 < x) :
    fiberWindowInverse x ≤ fiberWindowInverseRadical x := by
  have ha := (fiber_window_radical_domain hx).1
  have hw := fiber_window_inverse_positive hx
  have hq := fiber_window_radical_quadratic hx
  have hp := fiber_window_inverse_quadratic hx.le
  have hneg : -2 * x ^ 5 / (2 + 5 * x + 2 * x ^ 2) ^ 2 ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (by norm_num) (pow_nonneg hx.le 5)) (sq_nonneg _)
  have hpoly : (fiberWindowInverse x) ^ 2 + (2 + x) * fiberWindowInverse x - 2 * x ≤ 0 := by
    linarith only [hp,hneg]
  nlinarith only [hq,hpoly,ha,hw,hx]

/-- Both displayed inverse comparisons, with the printed unrestricted x>0. -/
theorem fiber_window_inverse_bounds {x : ℝ} (hx : 0 < x) :
    fiberWindowInverseRadical x ≤ fiberLambertW x ∧
      fiberWindowInverse x ≤ fiberWindowInverseRadical x := by
  exact ⟨fiber_lambert_lower_of_product hx (fiber_window_radical_domain hx).1.le
    (fiber_window_radical_cost hx),fiber_window_inverse_le_radical hx⟩

theorem fiber_window_inverse_root {x omega : ℝ} (hx : 0 < x)
    (hbound : x ≤ Real.exp (1 + omega)) :
    fiberWindowInverse x ≤ 1 + V22.rootMap omega := by
  have hb := (fiber_window_inverse_bounds hx).2.trans (fiber_window_inverse_bounds hx).1
  have hm := fiber_lambert_monotone hx hbound
  have he : fiberLambertW (Real.exp (1 + omega)) = 1 + V22.rootMap omega := by
    unfold fiberLambertW
    rw [Real.log_exp]
    congr 2
    ring
  rw [he] at hm
  exact hb.trans hm

end Erdos993Lean.Analytic.V213
