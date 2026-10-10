module

public import Erdos993Lean.Analytic.V213.FiberLowerQuadratic

/-!
Literal whole-domain second-order lower support for Q_(1/19).
The curvature premise is proved from its exact derivative formula. The
supporting line follows from ordinary convexity after subtracting the
printed quadratic, and includes t=t0 and the closed t=3/5 endpoint.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_convex_lower_tangent {f : ℝ → ℝ} {S : Set ℝ} {x y v : ℝ}
    (hc : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f v x) :
    f x + v * (y - x) ≤ f y := by
  rcases lt_trichotomy x y with hxy | he | hyx
  · have hs := hc.le_slope_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field] at hs
    have h := (le_div_iff₀ (sub_pos.mpr hxy)).mp hs
    linarith
  · subst y
    simp
  · have hs := hc.slope_le_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field] at hs
    have h := (div_le_iff₀ (sub_pos.mpr hyx)).mp hs
    linarith

noncomputable def fiberLowerQCorrected (a t : ℝ) : ℝ :=
  fiberLowerQ (1 / 19) a t - 9 / 2 * (t - (11 / 10 : ℝ) ^ 2) ^ 2

noncomputable def fiberLowerQCorrectedPrime (a t : ℝ) : ℝ :=
  fiberLowerQPrime (1 / 19) a t - 9 * (t - (11 / 10 : ℝ) ^ 2)

theorem fiber_hasDerivAt_lower_Q_corrected {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberLowerQCorrected a) (fiberLowerQCorrectedPrime a t) t := by
  have h := (fiber_hasDerivAt_lower_Q (z := 1 / 19) (a := a) ht).sub
    ((((hasDerivAt_id t).sub_const ((11 / 10 : ℝ) ^ 2)).pow 2).const_mul (9 / 2 : ℝ))
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberLowerQCorrectedPrime]
    ring

theorem fiber_hasDerivAt_lower_Q_correctedPrime {a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberLowerQCorrectedPrime a) (fiberLowerQSecond (1 / 19) a t - 9) t := by
  have h := (fiber_hasDerivAt_lower_QPrime (z := 1 / 19) (a := a) ht).sub
    (((hasDerivAt_id t).sub_const ((11 / 10 : ℝ) ^ 2)).const_mul (9 : ℝ))
  convert h using 1
  · funext x
    rfl
  · simp

theorem fiber_lower_Q_corrected_convex {a : ℝ} (ha : 0 ≤ a) :
    ConvexOn ℝ (Ici (3 / 5)) (fiberLowerQCorrected a) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fiberLowerQCorrectedPrime a)
    (f'' := fun t => fiberLowerQSecond (1 / 19) a t - 9) (convex_Ici _)
  · intro t ht
    have ht' : (3 / 5 : ℝ) ≤ t := ht
    exact (fiber_hasDerivAt_lower_Q_corrected (a := a) (by linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : (3 / 5 : ℝ) < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (fiber_hasDerivAt_lower_Q_corrected (a := a) (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht' : (3 / 5 : ℝ) < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact (fiber_hasDerivAt_lower_Q_correctedPrime (a := a) (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht' : (3 / 5 : ℝ) < t := by simpa only [interior_Ici, mem_Ioi] using ht
    exact sub_nonneg.mpr (fiber_lower_Q_curvature ha ht'.le)

theorem fiber_lower_Q_tangent {a t : ℝ} (ha : 0 ≤ a) (ht : 3 / 5 ≤ t) :
    fiberLowerQ (1 / 19) a ((11 / 10 : ℝ) ^ 2) +
      fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2) * (t - (11 / 10 : ℝ) ^ 2) +
        9 / 2 * (t - (11 / 10 : ℝ) ^ 2) ^ 2 ≤ fiberLowerQ (1 / 19) a t := by
  have hc := fiber_lower_Q_corrected_convex ha
  have h := fiber_convex_lower_tangent hc (by norm_num : (11 / 10 : ℝ) ^ 2 ∈ Ici (3 / 5)) ht
    (fiber_hasDerivAt_lower_Q_corrected (a := a) (t := (11 / 10 : ℝ) ^ 2) (by norm_num))
  simp only [fiberLowerQCorrected, fiberLowerQCorrectedPrime, sub_self, mul_zero, sub_zero,
    zero_pow (by decide : 2 ≠ 0)] at h
  linarith

end Erdos993Lean.Analytic.V213
