module

public import Erdos993Lean.Analytic.V213.FiberEntropy

/-!
The literal degree-eight even upper Taylor bound on negative
arguments and degree-four lower bound on positive arguments used in Eq87.
All arguments are real and the finite sums are the printed factorial sums.
No finite DF10 data is consumed.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

noncomputable def fiberWingTaylor4 (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24
noncomputable def fiberWingTaylor8 (x : ℝ) : ℝ :=
  fiberWingTaylor4 x + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040 + x ^ 8 / 40320
noncomputable def fiberWingTaylor8Deriv (x : ℝ) : ℝ :=
  1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120 + x ^ 6 / 720 + x ^ 7 / 5040

theorem fiber_wing_taylor4_sum (x : ℝ) :
    fiberWingTaylor4 x = ∑ h ∈ Finset.range 5, x ^ h / (h.factorial : ℝ) := by
  norm_num [fiberWingTaylor4,Finset.sum_range_succ,Nat.factorial]

theorem fiber_wing_taylor8_sum (x : ℝ) :
    fiberWingTaylor8 x = ∑ h ∈ Finset.range 9, x ^ h / (h.factorial : ℝ) := by
  norm_num [fiberWingTaylor8,fiberWingTaylor4,Finset.sum_range_succ,Nat.factorial]

theorem fiber_hasDerivAt_wing_taylor8 (x : ℝ) :
    HasDerivAt fiberWingTaylor8 (fiberWingTaylor8Deriv x) x := by
  convert ((((((((hasDerivAt_id x).const_add 1).add ((hasDerivAt_pow 2 x).div_const 2)).add
    ((hasDerivAt_pow 3 x).div_const 6)).add ((hasDerivAt_pow 4 x).div_const 24)).add
    ((hasDerivAt_pow 5 x).div_const 120)).add ((hasDerivAt_pow 6 x).div_const 720)).add
    ((hasDerivAt_pow 7 x).div_const 5040)).add ((hasDerivAt_pow 8 x).div_const 40320) using 1
  · rfl
  · norm_num [fiberWingTaylor8Deriv]
    ring

theorem fiber_wing_taylor8_negative_identity (z : ℝ) :
    fiberWingTaylor8 (-z) - fiberWingTaylor8Deriv (-z) = z ^ 8 / 40320 := by
  unfold fiberWingTaylor8 fiberWingTaylor4 fiberWingTaylor8Deriv
  ring

theorem fiber_wing_exp_negative_upper {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-z) ≤ fiberWingTaylor8 (-z) := by
  let f : ℝ → ℝ := fun y => Real.exp y * fiberWingTaylor8 (-y) - 1
  have hd (y : ℝ) : HasDerivAt f (Real.exp y * y ^ 8 / 40320) y := by
    have ht := (fiber_hasDerivAt_wing_taylor8 (-y)).comp y ((hasDerivAt_id y).neg)
    convert (((hasDerivAt_id y).exp.mul ht).sub_const 1) using 1
    · rfl
    · dsimp
      have hi := fiber_wing_taylor8_negative_identity y
      calc
        Real.exp y * y ^ 8 / 40320 = Real.exp y * (y ^ 8 / 40320) := by ring
        _ = Real.exp y * (fiberWingTaylor8 (-y) - fiberWingTaylor8Deriv (-y)) := by rw [hi]
        _ = _ := by ring
  have hm : MonotoneOn f (Icc (0 : ℝ) z) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 z)
      (fun y _ => (hd y).continuousAt.continuousWithinAt)
      (fun y _ => (hd y).hasDerivWithinAt)
      (fun y _ => by positivity)
  have h := hm ⟨le_rfl,hz⟩ ⟨hz,le_rfl⟩ hz
  have h0 : f 0 = 0 := by norm_num [f,fiberWingTaylor8,fiberWingTaylor4]
  rw [h0] at h
  dsimp [f] at h
  have hb : 1 / Real.exp z ≤ fiberWingTaylor8 (-z) := by
    apply (div_le_iff₀ (Real.exp_pos z)).2
    nlinarith only [h]
  simpa only [Real.exp_neg,one_div] using hb

theorem fiber_wing_exp_positive_lower {x : ℝ} (hx : 0 ≤ x) :
    fiberWingTaylor4 x ≤ Real.exp x := by
  rw [fiber_wing_taylor4_sum]
  exact Real.sum_le_exp_of_nonneg hx 5

end Erdos993Lean.Analytic.V213
