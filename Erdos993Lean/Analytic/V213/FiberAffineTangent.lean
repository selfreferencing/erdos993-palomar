module

public import Erdos993Lean.Analytic.V213.FiberAffineCurvature

/-!
The literal second-order tangent support for H_beta on the complete closed
t domain[3/4,infinity). Curvature is discharged by its proved exact formula;
A,V,c are bound to reviewed F03. The full discriminant and positive c give
H_beta>=587/(1800c)>=587/16200>1/28, including both w/beta endpoints.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberAffineSupportCorrected (beta w t : ℝ) : ℝ :=
  fiberAffineSupport beta t w - fiberAffineCurvature w / 2 * (t - 1) ^ 2

noncomputable def fiberAffineSupportCorrectedPrime (beta w t : ℝ) : ℝ :=
  fiberAffineSupportPrime beta t w - fiberAffineCurvature w * (t - 1)

theorem fiber_hasDerivAt_affine_corrected {beta w t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberAffineSupportCorrected beta w) (fiberAffineSupportCorrectedPrime beta w t) t := by
  have h := (fiber_hasDerivAt_affine_support (beta := beta) (w := w) ht).sub
    ((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (fiberAffineCurvature w / 2))
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberAffineSupportCorrectedPrime]
    ring

theorem fiber_hasDerivAt_affine_correctedPrime {beta w t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberAffineSupportCorrectedPrime beta w) (fiberAffineSupportSecond t w - fiberAffineCurvature w) t := by
  have h := (fiber_hasDerivAt_affine_supportPrime (beta := beta) (w := w) ht).sub
    (((hasDerivAt_id t).sub_const 1).const_mul (fiberAffineCurvature w))
  convert h using 1
  · funext x
    rfl
  · simp

theorem fiber_affine_corrected_convex {beta w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    ConvexOn ℝ (Ici (3 / 4)) (fiberAffineSupportCorrected beta w) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fiberAffineSupportCorrectedPrime beta w)
    (f'' := fun t => fiberAffineSupportSecond t w - fiberAffineCurvature w) (convex_Ici _)
  · intro t ht
    have ht' : (3 / 4 : ℝ) ≤ t := ht
    exact (fiber_hasDerivAt_affine_corrected (beta := beta) (w := w) (by linarith)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : (3 / 4 : ℝ) < t := by simpa only [interior_Ici,mem_Ioi] using ht
    exact (fiber_hasDerivAt_affine_corrected (beta := beta) (w := w) (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht' : (3 / 4 : ℝ) < t := by simpa only [interior_Ici,mem_Ioi] using ht
    exact (fiber_hasDerivAt_affine_correctedPrime (beta := beta) (w := w) (by linarith)).hasDerivWithinAt
  · intro t ht
    have ht' : (3 / 4 : ℝ) < t := by simpa only [interior_Ici,mem_Ioi] using ht
    exact sub_nonneg.mpr (fiber_affine_support_curvature ht'.le hw0 hwh)

theorem fiber_affine_tangent_support {beta t w : ℝ} (ht : 3 / 4 ≤ t)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    fiberAffineA w + (fiberAffineV w - beta) * (t - 1) +
      fiberAffineCurvature w / 2 * (t - 1) ^ 2 ≤ fiberAffineSupport beta t w := by
  have h := fiber_convex_lower_tangent (fiber_affine_corrected_convex (beta := beta) hw0 hwh)
    (by norm_num : (1 : ℝ) ∈ Ici (3 / 4)) ht
    (fiber_hasDerivAt_affine_corrected (beta := beta) (w := w) (t := 1) (by norm_num))
  simp only [fiberAffineSupportCorrected,fiberAffineSupportCorrectedPrime,sub_self,mul_zero,
    zero_pow (by decide +kernel : 2 ≠ 0),sub_zero] at h
  rw [(fiber_affine_support_at_one beta w).1,(fiber_affine_support_at_one beta w).2] at h
  linarith only [h]

theorem fiber_affine_support_discriminant {beta t w : ℝ} (ht : 3 / 4 ≤ t)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hb0 : 0 ≤ beta) (hbh : beta ≤ 1) :
    587 / (1800 * fiberAffineCurvature w) ≤ fiberAffineSupport beta t w := by
  have hc := (fiber_affine_curvature_bounds hw0 hwh).1
  have hc0 : 0 < fiberAffineCurvature w := by linarith only [hc]
  have hquad := fiber_affine_tangent_support (beta := beta) ht hw0 hwh
  have hmul := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 2 * fiberAffineCurvature w)
  have hdis := fiber_affine_tangent_discriminant hw0 hwh hb0 hbh
  have hs := sq_nonneg (fiberAffineCurvature w * (t - 1) + (fiberAffineV w - beta))
  apply (div_le_iff₀ (by positivity : 0 < 1800 * fiberAffineCurvature w)).2
  nlinarith only [hmul,hdis,hs]

theorem fiber_affine_support_margin {beta t w : ℝ} (ht : 3 / 4 ≤ t)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hb0 : 0 ≤ beta) (hbh : beta ≤ 1) :
    (1 / 28 : ℝ) < fiberAffineSupport beta t w := by
  have hc := fiber_affine_curvature_bounds hw0 hwh
  have hc0 : 0 < fiberAffineCurvature w := by linarith only [hc.1]
  have hr : (587 / 16200 : ℝ) ≤ 587 / (1800 * fiberAffineCurvature w) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (by linarith only [hc.2])
  exact fiber_affine_final_margin.trans_le (hr.trans (fiber_affine_support_discriminant ht hw0 hwh hb0 hbh))

end Erdos993Lean.Analytic.V213
