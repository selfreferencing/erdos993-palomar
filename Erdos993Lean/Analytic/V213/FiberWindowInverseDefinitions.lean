module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus
public import Erdos993Lean.Analytic.V213.FreeCountRealLogEnvelopes

/-!
Eq102: the actual positive inverse W(x) of z*exp(z), defined from
the accepted unique root of s+log(1+s). The rational function is the
literal printed formula, not a replacement endpoint definition.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberLambertW (x : ℝ) : ℝ := 1 + V22.rootMap (Real.log x - 1)

noncomputable def fiberWindowInverse (x : ℝ) : ℝ := x * (2 + 3 * x) / (2 + 5 * x + 2 * x ^ 2)

noncomputable def fiberWindowInverseRadical (x : ℝ) : ℝ :=
  4 * x / (Real.sqrt (4 + 12 * x + x ^ 2) + 2 + x)

theorem fiber_lambert_positive (x : ℝ) : 0 < fiberLambertW x := by
  unfold fiberLambertW
  linarith [shared_rootMap_gt_neg_one (Real.log x - 1)]

theorem fiber_lambert_equation {x : ℝ} (hx : 0 < x) :
    fiberLambertW x * Real.exp (fiberLambertW x) = x := by
  have hp := fiber_lambert_positive x
  have hr := shared_rootMap_equation (Real.log x - 1)
  have he : fiberLambertW x + Real.log (fiberLambertW x) = Real.log x := by
    unfold fiberLambertW
    linarith only [hr]
  have h := congrArg Real.exp he
  rw [Real.exp_add,Real.exp_log hp,Real.exp_log hx] at h
  simpa only [mul_comm] using h

theorem fiber_positive_exp_product_strict {z y : ℝ} (hz : 0 ≤ z) (hzy : z < y) :
    z * Real.exp z < y * Real.exp y := by
  have hy : 0 ≤ y := hz.trans hzy.le
  calc
    z * Real.exp z < y * Real.exp z := mul_lt_mul_of_pos_right hzy (Real.exp_pos z)
    _ ≤ y * Real.exp y := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hzy.le) hy

theorem fiber_lambert_lower_of_product {x z : ℝ} (hx : 0 < x) (hz : 0 ≤ z)
    (hcost : z * Real.exp z ≤ x) : z ≤ fiberLambertW x := by
  by_contra h
  have hlt : fiberLambertW x < z := lt_of_not_ge h
  have hs := fiber_positive_exp_product_strict (fiber_lambert_positive x).le hlt
  rw [fiber_lambert_equation hx] at hs
  linarith

theorem fiber_lambert_monotone {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    fiberLambertW x ≤ fiberLambertW y := by
  unfold fiberLambertW
  have h := shared_rootMap_monotone (show Real.log x - 1 ≤ Real.log y - 1 from
    sub_le_sub_right (Real.log_le_log hx hxy) 1)
  linarith

/-- The printed elementary exponential comparison, on its entire domain. -/
theorem fiber_exp_pade_upper {z : ℝ} (hz0 : 0 ≤ z) (hz2 : z < 2) :
    Real.exp z ≤ (2 + z) / (2 - z) := by
  have h := (FreeCountVariance.Envelopes.artanh_brackets
    (show 0 ≤ z / 2 by linarith) (show z / 2 < 1 by linarith)).1
  have h3 : 0 ≤ (z / 2) ^ 3 / 3 := by positivity
  have h5 : 0 ≤ (z / 2) ^ 5 / 5 := by positivity
  have hratio : (1 + z / 2) / (1 - z / 2) = (2 + z) / (2 - z) := by
    field_simp [ne_of_gt (by linarith : 0 < 2 - z)] <;> ring
  rw [hratio] at h
  unfold FreeCountVariance.Envelopes.seriesS at h
  have hlog : z ≤ Real.log ((2 + z) / (2 - z)) := by linarith
  have hp : 0 < (2 + z) / (2 - z) := by
    apply div_pos <;> linarith
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log hp] at he

theorem fiber_window_inverse_positive {x : ℝ} (hx : 0 < x) :
    0 < fiberWindowInverse x := by
  unfold fiberWindowInverse
  positivity

theorem fiber_hasDerivAt_window_inverse {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt fiberWindowInverse
      ((4 + 12 * x + 11 * x ^ 2) / (2 + 5 * x + 2 * x ^ 2) ^ 2) x := by
  have hd : 0 < 2 + 5 * x + 2 * x ^ 2 := by positivity
  have hn := (hasDerivAt_id x).mul (((hasDerivAt_id x).const_mul 3).const_add 2)
  have hden := ((((hasDerivAt_id x).const_mul 5).const_add 2).add
    ((hasDerivAt_pow 2 x).const_mul 2))
  convert hn.div hden hd.ne' using 1
  · funext y
    rfl
  · dsimp
    field_simp [hd.ne'] <;> ring

theorem fiber_window_inverse_increases : StrictMonoOn fiberWindowInverse (Ici (0 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _)
  · intro x hx
    exact (fiber_hasDerivAt_window_inverse hx).continuousAt.continuousWithinAt
  · intro x hx
    have h : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    exact (fiber_hasDerivAt_window_inverse h.le).hasDerivWithinAt
  · intro x hx
    have h : 0 < x := by simpa only [interior_Ici,mem_Ioi] using hx
    positivity

theorem fiber_window_inverse_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    fiberWindowInverse x ≤ 5 / 9 := by
  have h := fiber_window_inverse_increases.monotoneOn hx0 (show (1 : ℝ) ∈ Ici 0 by norm_num) hx1
  norm_num [fiberWindowInverse] at h
  exact h

end Erdos993Lean.Analytic.V213
