module

public import Erdos993Lean.Analytic.V213.FiberAffineMonotonicity

/-!
Whole-domain monotonicity and actual-skew substitution for the Y
minorant in Theorem6.15. Both closed xi endpoints
and the gamma>=1+21*16/625>3/2 window guard are proved. No statement
about monotonicity of an integer-index binomial mass is substituted.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_affine_xi_square {xi : ℝ} (hx0 : 0 ≤ xi)
    (hxh : xi ≤ 1 / Real.sqrt (3 : ℝ)) : xi ^ 2 ≤ 1 / 3 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hb := (le_div_iff₀ hs).mp hxh
  have hx : 0 ≤ xi * Real.sqrt (3 : ℝ) := by positivity
  have hq : (xi * Real.sqrt (3 : ℝ)) ^ 2 ≤ 1 := by nlinarith only [hb, hx]
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)] at hq
  linarith only [hq]

theorem fiber_affine_Y_derivative_pos {N w xi : ℝ} (hN : 22 ≤ N)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hxil : 4 / 25 ≤ xi)
    (hxih : xi ≤ 1 / Real.sqrt (3 : ℝ)) : 0 < deriv (fiberAffineY N w) xi := by
  rw [(fiber_hasDerivAt_affine_Y hN w xi).deriv]
  have hs := fiber_affine_Y_derivative_sign hN hw0 hwh hxil
    (fiber_affine_xi_square (by linarith) hxih)
  have hh : 0 < fiberAffineH N := lt_of_lt_of_le (by norm_num) (fiber_affine_H_lower hN)
  exact mul_pos (mul_pos hh (Real.exp_pos _)) (lt_of_lt_of_le (by norm_num) hs)

theorem fiber_affine_Y_strictMono {N w : ℝ} (hN : 22 ≤ N)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    StrictMonoOn (fiberAffineY N w) (Icc (4 / 25) (1 / Real.sqrt (3 : ℝ))) := by
  have hc : ContinuousOn (fiberAffineY N w) (Icc (4 / 25) (1 / Real.sqrt (3 : ℝ))) := by
    intro xi hxi
    exact (fiber_hasDerivAt_affine_Y hN w xi).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hc
  intro xi hxi
  have hx := interior_subset hxi
  exact fiber_affine_Y_derivative_pos hN hw0 hwh hx.1 hx.2

theorem fiber_affine_skew_xi_bounds {r : ℝ} (hrl : 4 / 25 ≤ r) (hrh : r ≤ 1 / 2) :
    4 / 25 ≤ r / Real.sqrt (1 - r ^ 2) ∧
      r / Real.sqrt (1 - r ^ 2) ≤ 1 / Real.sqrt (3 : ℝ) := by
  have hr0 : 0 ≤ r := by linarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hrh, hr0]
  have hs : 0 < Real.sqrt (1 - r ^ 2) := Real.sqrt_pos.2 ha
  have hsq := Real.sq_sqrt ha.le
  have hs1 : Real.sqrt (1 - r ^ 2) ≤ 1 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by norm_num, by nlinarith only [sq_nonneg r]⟩
  constructor
  · have hb : r ≤ r / Real.sqrt (1 - r ^ 2) := by
      apply (le_div_iff₀ hs).2
      nlinarith only [hs1, hr0]
    exact hrl.trans hb
  · have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    apply (div_le_div_iff₀ hs hs3).2
    apply (sq_le_sq₀ (by positivity : 0 ≤ r * Real.sqrt (3 : ℝ))
      (by positivity : 0 ≤ 1 * Real.sqrt (1 - r ^ 2))).1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), one_mul, hsq]
    nlinarith only [hrh, hr0]

theorem fiber_affine_Y_at_skew_lower {N w r : ℝ} (hN : 22 ≤ N)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hrl : 4 / 25 ≤ r) (hrh : r ≤ 1 / 2) :
    fiberAffineY N w (4 / 25) ≤ fiberAffineY N w (r / Real.sqrt (1 - r ^ 2)) := by
  have hb := fiber_affine_skew_xi_bounds hrl hrh
  exact (fiber_affine_Y_strictMono hN hw0 hwh).monotoneOn ⟨le_refl _, hb.1.trans hb.2⟩ hb hb.1

theorem fiber_affine_gamma_formula {N r : ℝ} (hN : 22 ≤ N)
    (hrl : 4 / 25 ≤ r) (hrh : r ≤ 1 / 2) :
    V22.gamma r N = 1 + fiberAffineH N * (r / Real.sqrt (1 - r ^ 2)) ^ 2 := by
  have hn : 0 < N := by linarith
  have hr0 : 0 ≤ r := by linarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hrh, hr0]
  have hs := Real.sq_sqrt ha.le
  unfold V22.gamma V22.Delta fiberAffineH
  rw [div_pow, hs]
  field_simp [hn.ne', ha.ne']

theorem fiber_affine_gamma_lower {N r : ℝ} (hN : 22 ≤ N)
    (hrl : 4 / 25 ≤ r) (hrh : r ≤ 1 / 2) :
    1 + 21 * (16 / 625 : ℝ) ≤ V22.gamma r N ∧ (3 / 2 : ℝ) < V22.gamma r N := by
  have hh := fiber_affine_H_lower hN
  have hx := (fiber_affine_skew_xi_bounds hrl hrh).1
  have hx2 : (16 / 625 : ℝ) ≤ (r / Real.sqrt (1 - r ^ 2)) ^ 2 := by nlinarith only [hx]
  have hm := mul_le_mul (by exact hh) hx2 (by norm_num : (0 : ℝ) ≤ 16 / 625)
    (by linarith only [hh] : 0 ≤ fiberAffineH N)
  rw [fiber_affine_gamma_formula hN hrl hrh]
  constructor <;> nlinarith only [hm]

end Erdos993Lean.Analytic.V213
