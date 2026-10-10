module

public import Erdos993Lean.Analytic.V213.FiberRayRegional

/-!
Actual beta_e is monotone on the complete real domain N>=10
for 0<=R<=7/20, including the closed min-cap join. The pre-cap
derivative is at least 1/5 and the fixed-cap tail is termwise monotone.
The closed-interval congruence/splice proof follows the generic argument
for capped coefficient monotonicity,
with every old finite endpoint/margin premise discharged here.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_capped_beta_pre {R N : ℝ}
    (hR : 0 < R) (hRh : R ≤ 1 / 2) (hN : 0 < N) (hcap : N ≤ (6 / R) ^ 2) :
    fiberRayCappedBeta R N = fiberRayCalc_preCapBeta R N := by
  unfold fiberRayCappedBeta
  rw [fiber_ray_cap_pre hR hcap]
  unfold fiberRayBeta fiberRayCalc_preCapBeta
  rw [fiberRayCalc_preCapE2_eq hR.le hRh hN]

theorem fiber_ray_pre_beta_derivative_lower {R N : ℝ}
    (hR : 0 < R) (hRh : R ≤ 7 / 20) (hN : 10 ≤ N) (hcap : N ≤ (6 / R) ^ 2) :
    (1 / 5 : ℝ) ≤ fiberRayCalc_preCapBetaDerivative R N := by
  have hRh' : R ≤ 1 / 2 := by linarith only [hRh]
  have hrs := fiber_ray_regional_rho hN hR.le hRh
  have hrsp : 0 < rhoStar N R := by linarith only [hrs]
  have hq : 2 / rhoStar N R ≤ (4 : ℝ) := by
    apply (div_le_iff₀ hrsp).2
    linarith only [hrs]
  have heD := (fiber_ray_pre_derivative_d0 hR hRh' (by norm_num : (0 : ℝ) < 10) hN hcap).trans
    (fiber_ray_regional_d0 (by norm_num : (10 : ℝ) ≤ 10) hR.le hRh)
  have heD0 := fiberRayCalc_preCapE2Derivative_nonneg (N := N) hR.le hRh'
  have hprod := mul_le_mul hq heD heD0 (by norm_num : (0 : ℝ) ≤ 4)
  have he := fiberRayCalc_preCapE2_nonneg hR.le hRh' (by linarith only [hN] : 0 < N)
  have hrD := fiberRayCalc_rhoStarDerivative_nonneg hR.le hRh' (by linarith only [hN] : 1 < N)
  have hc : 0 ≤ 2 * fiberRayCalc_preCapE2 R N * fiberRayCalc_rhoStarDerivative R N /
      (rhoStar N R) ^ 2 := by positivity
  unfold fiberRayCalc_preCapBetaDerivative
  norm_num at hprod
  linarith only [hprod,hc]

theorem fiber_ray_capped_beta_deriv_pre {R N : ℝ}
    (hR : 0 < R) (hRh : R ≤ 7 / 20) (hN : N ∈ Set.Icc 10 ((6 / R) ^ 2)) :
    HasDerivWithinAt (fiberRayCappedBeta R) (fiberRayCalc_preCapBetaDerivative R N)
      (Set.Icc 10 ((6 / R) ^ 2)) N := by
  have hrs := fiber_ray_regional_rho hN.1 hR.le hRh
  have hRh' : R ≤ 1 / 2 := by linarith only [hRh]
  exact (fiberRayCalc_preCapBeta_hasDerivAt hR.le hRh'
    (by linarith only [hN.1]) (by linarith only [hrs])).hasDerivWithinAt.congr_of_mem
      (fun n hn => fiber_ray_capped_beta_pre hR hRh' (by linarith only [hn.1]) hn.2) hN

theorem fiber_ray_capped_beta_monotone_pre {R : ℝ}
    (hR : 0 < R) (hRh : R ≤ 7 / 20) :
    MonotoneOn (fiberRayCappedBeta R) (Set.Icc 10 ((6 / R) ^ 2)) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro n hn
    exact (fiber_ray_capped_beta_deriv_pre hR hRh hn).continuousWithinAt
  · intro n hn
    exact (fiber_ray_capped_beta_deriv_pre hR hRh (interior_subset hn)).mono interior_subset
  · intro n hn
    have hclosed := interior_subset hn
    exact (by norm_num : (0 : ℝ) ≤ 1 / 5).trans
      (fiber_ray_pre_beta_derivative_lower hR hRh hclosed.1 hclosed.2)

theorem fiber_ray_capped_beta_monotone_tail {R : ℝ}
    (hR : 0 < R) (hRh : R ≤ 7 / 20) :
    MonotoneOn (fiberRayCappedBeta R) (Set.Ici (max 10 ((6 / R) ^ 2))) := by
  intro x hx y hy hxy
  have hx10 : 10 ≤ x := le_max_left _ _ |>.trans hx
  have hy10 : 10 ≤ y := hx10.trans hxy
  have hxcap : (6 / R) ^ 2 ≤ x := le_max_right _ _ |>.trans hx
  have hycap : (6 / R) ^ 2 ≤ y := hxcap.trans hxy
  unfold fiberRayCappedBeta
  rw [fiber_ray_cap_tail hR hxcap,fiber_ray_cap_tail hR hycap]
  exact fiber_ray_beta_fixed_monotone hR.le (by linarith only [hRh]) (by norm_num)
    hx10 hy10 hxy

/-- Whole-domain monotonicity, with both sides and the cap itself included. -/
theorem fiber_ray_capped_beta_monotone {R : ℝ}
    (hR : 0 ≤ R) (hRh : R ≤ 7 / 20) :
    MonotoneOn (fiberRayCappedBeta R) (Set.Ici 10) := by
  by_cases hRp : 0 < R
  · have hpre := fiber_ray_capped_beta_monotone_pre hRp hRh
    have htail := fiber_ray_capped_beta_monotone_tail hRp hRh
    intro x hx y hy hxy
    by_cases hxcap : x ≤ (6 / R) ^ 2
    · by_cases hycap : y ≤ (6 / R) ^ 2
      · exact hpre ⟨hx,hxcap⟩ ⟨hy,hycap⟩ hxy
      · have hc10 : 10 ≤ (6 / R) ^ 2 := hx.trans hxcap
        exact (hpre ⟨hx,hxcap⟩ ⟨hc10,le_refl _⟩ hxcap).trans
          (htail (max_le hc10 (le_refl _)) (max_le hy (le_of_not_ge hycap)) (le_of_not_ge hycap))
    · exact htail (max_le hx (le_of_not_ge hxcap))
        (max_le hy ((le_of_not_ge hxcap).trans hxy)) hxy
  · have hR0 : R = 0 := by linarith only [hR,hRp]
    subst R
    have heq (N : ℝ) : fiberRayCappedBeta 0 N = fiberRayBeta N 0 0 := by
      simp [fiberRayCappedBeta,fiberRayZeta]
    intro x hx y hy hxy
    rw [heq,heq]
    exact fiber_ray_beta_fixed_monotone (by norm_num : (0 : ℝ) ≤ 0)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 0) hx hy hxy

end Erdos993Lean.Analytic.V213
