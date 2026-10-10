module

public import Erdos993Lean.Analytic.V213.FiberDefinitions

/-!
The whole positive-ray decrease used in both Eq91/92. The
threshold is the actual d*x0>=3/2. No finite sampled mean or integral
approximation replaces the all-real half-line statement.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set Real

noncomputable def fiberTailDecay (d x : ℝ) : ℝ := x^(3/2 : ℝ)*Real.exp (-d*x)

theorem fiber_tail_decay_deriv {d x : ℝ} (hx : 0 < x) :
    HasDerivAt (fiberTailDecay d) (x^(1/2 : ℝ)*Real.exp (-d*x)*(3/2-d*x)) x := by
  have hr := Real.hasDerivAt_rpow_const (x := x) (p := (3/2 : ℝ)) (Or.inl hx.ne')
  have he := (((hasDerivAt_id x).const_mul (-d)).exp)
  have hid : x^(3/2 : ℝ) = x^(1/2 : ℝ)*x := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,Real.rpow_add hx,Real.rpow_one]
  convert hr.mul he using 1
  · rfl
  · rw [hid]
    norm_num only [show (3/2 : ℝ)-1=1/2 by norm_num]
    dsimp
    ring

theorem fiber_tail_decay_antitone {d x0 : ℝ} (hd : 0 < d) (hx0 : 0 < x0)
    (hthreshold : 3/2 ≤ d*x0) : AntitoneOn (fiberTailDecay d) (Ici x0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici x0)
  · intro x hx
    exact (fiber_tail_decay_deriv (hx0.trans_le hx)).continuousAt.continuousWithinAt
  · intro x hx
    exact (fiber_tail_decay_deriv (hx0.trans_le (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    have hx' := interior_subset hx
    have ht := hthreshold.trans (mul_le_mul_of_nonneg_left hx' hd.le)
    exact mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (Real.rpow_nonneg (hx0.trans_le hx').le _) (Real.exp_pos _).le)
      (by linarith only [ht])

theorem fiber_tail_decay_bound {d x0 x : ℝ} (hd : 0 < d) (hx0 : 0 < x0)
    (hthreshold : 3/2 ≤ d*x0) (hx : x0 ≤ x) :
    x^(3/2 : ℝ)*Real.exp (-d*x) ≤ x0^(3/2 : ℝ)*Real.exp (-d*x0) :=
  fiber_tail_decay_antitone hd hx0 hthreshold (le_refl x0) hx hx

end Erdos993Lean.Analytic.V213
