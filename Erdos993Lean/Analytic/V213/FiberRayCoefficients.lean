module

public import Erdos993Lean.Analytic.V213.FiberCoefficientBounds
public import Erdos993Lean.Analytic.V213.FiberUniformConsequences

/-!
Actual Eq93 coefficients.
The full reciprocal-loss expression is proved antitone in N, rather than
only its component bounds. Fixed-zeta and exact cap branches are generic
analytic facts. No reviewed finite record is consumed in this module.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberRayE2 (N R zeta : ℝ) : ℝ :=
  V22.e2 + V22.e3 R * zeta + V22.e4 N R * zeta ^ 2 + V22.e5 R * zeta ^ 3

noncomputable def fiberRayZeta (R N : ℝ) : ℝ := min 6 (R * Real.sqrt N)

noncomputable def fiberRayBeta (N R zeta : ℝ) : ℝ :=
  N - 1 - 2 / V22.rhoStar N R * fiberRayE2 N R zeta

noncomputable def fiberRayCappedBeta (R N : ℝ) : ℝ := fiberRayBeta N R (fiberRayZeta R N)

noncomputable def fiberRayD0 (R N0 : ℝ) : ℝ :=
  5 * R / (12 * (1 - R ^ 2) * Real.sqrt N0) + 5 * R ^ 2 / (6 * (1 - R ^ 2) ^ 2)

theorem fiber_ray_E2_formula (N R zeta : ℝ) :
    fiberRayE2 N R zeta = 1 / 2 + 5 * zeta / (6 * (1 - R ^ 2)) +
      (N + 1) * zeta ^ 2 / (12 * N * (1 - R ^ 2) ^ 2) +
      zeta ^ 3 / (12 * (1 - R ^ 2) ^ 2) := by
  unfold fiberRayE2 V22.e2 V22.e3 V22.e4 V22.e5
  ring

theorem fiber_ray_beta_formula (N R zeta : ℝ) :
    fiberRayBeta N R zeta = N - 1 - 2 * fiberRayE2 N R zeta / V22.rhoStar N R := by
  unfold fiberRayBeta
  ring

theorem fiber_ray_E2_nonneg {N R zeta : ℝ} (hN : 0 < N)
    (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) (hz : 0 ≤ zeta) : 0 ≤ fiberRayE2 N R zeta := by
  have ho : 0 < 1 - R ^ 2 := by
    have hs := (sq_le_sq₀ hR (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hRh
    norm_num at hs
    linarith
  unfold fiberRayE2 V22.e2 V22.e3 V22.e4 V22.e5
  positivity

theorem fiber_ray_reciprocal_antitone {R : ℝ} (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) :
    AntitoneOn (fun N => (V22.rhoStar N R)⁻¹) (Set.Ici 10) := by
  rcases fiber_upper_coefficient_monotonicity hR hRh with ⟨_,_,_,_,_,hmono⟩
  intro N hN M hM hNM
  have hpos : 0 < V22.rhoStar N R := by linarith [fiber_rhoStar_precise_lower hN hR hRh]
  exact inv_anti₀ hpos (hmono hN hM hNM)

theorem fiber_ray_full_loss_antitone {R zeta : ℝ}
    (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) (hz : 0 ≤ zeta) :
    AntitoneOn (fun N => (4 * zeta + V22.kappaA N R * zeta ^ 2) / V22.rhoStar N R)
      (Set.Ici 10) := by
  rcases fiber_upper_coefficient_monotonicity hR hRh with ⟨hkap,_,_,_,_,hrho⟩
  intro N hN M hM hNM
  have hn : 0 < V22.rhoStar N R := by linarith [fiber_rhoStar_precise_lower hN hR hRh]
  have hm : 0 < V22.rhoStar M R := by linarith [fiber_rhoStar_precise_lower hM hR hRh]
  have ho : 0 < 1 - R ^ 2 := by
    have hs := (sq_le_sq₀ hR (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hRh
    norm_num at hs
    linarith
  have hk : 0 ≤ V22.kappaA N R := by
    unfold V22.kappaA
    have hn0 : 0 < N := by linarith [show (10 : ℝ) ≤ N from hN]
    positivity
  have hnum : 0 ≤ 4 * zeta + V22.kappaA N R * zeta ^ 2 := by positivity
  have horder : 4 * zeta + V22.kappaA M R * zeta ^ 2 ≤
      4 * zeta + V22.kappaA N R * zeta ^ 2 :=
    add_le_add (le_refl (4 * zeta)) (mul_le_mul_of_nonneg_right (hkap hN hM hNM) (sq_nonneg zeta))
  calc
    _ ≤ (4 * zeta + V22.kappaA N R * zeta ^ 2) / V22.rhoStar M R :=
      div_le_div_of_nonneg_right horder hm.le
    _ ≤ _ := div_le_div_of_nonneg_left hnum hn (hrho hN hM hNM)

theorem fiber_ray_E2_fixed_antitone {R zeta : ℝ} (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) :
    AntitoneOn (fun N => fiberRayE2 N R zeta) (Set.Ici 10) := by
  rcases fiber_upper_coefficient_monotonicity hR hRh with ⟨_,_,_,he4,_,_⟩
  intro N hN M hM hNM
  have h := mul_le_mul_of_nonneg_right (he4 hN hM hNM) (sq_nonneg zeta)
  change V22.e4 M R * zeta ^ 2 ≤ V22.e4 N R * zeta ^ 2 at h
  unfold fiberRayE2
  linarith

theorem fiber_ray_beta_fixed_monotone {R zeta : ℝ}
    (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) (hz : 0 ≤ zeta) :
    MonotoneOn (fun N => fiberRayBeta N R zeta) (Set.Ici 10) := by
  intro N hN M hM hNM
  have hn : 0 < V22.rhoStar N R := by linarith [fiber_rhoStar_precise_lower hN hR hRh]
  have hi := fiber_ray_reciprocal_antitone hR hRh hN hM hNM
  have he := fiber_ray_E2_fixed_antitone (zeta := zeta) hR hRh hN hM hNM
  have hep := fiber_ray_E2_nonneg (by linarith [show (10 : ℝ) ≤ M from hM] : 0 < M) hR hRh hz
  have hprod := mul_le_mul hi he hep (inv_nonneg.mpr hn.le)
  unfold fiberRayBeta
  simp only [div_eq_mul_inv] at *
  nlinarith only [hprod, hNM]

theorem fiber_ray_cap_pre {R N : ℝ} (hR : 0 < R) (hN : N ≤ (6 / R) ^ 2) :
    fiberRayZeta R N = R * Real.sqrt N := by
  have hs : Real.sqrt N ≤ 6 / R := Real.sqrt_le_iff.mpr ⟨by positivity, hN⟩
  have hz : R * Real.sqrt N ≤ 6 := by
    simpa only [mul_comm] using (le_div_iff₀ hR).mp hs
  exact min_eq_right hz

theorem fiber_ray_cap_tail {R N : ℝ} (hR : 0 < R) (hN : (6 / R) ^ 2 ≤ N) :
    fiberRayZeta R N = 6 := by
  have hs : 6 / R ≤ Real.sqrt N := by
    have h := Real.sqrt_le_sqrt hN
    simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 6 / R)] using h
  have hz : 6 ≤ R * Real.sqrt N := by
    simpa only [mul_comm] using (div_le_iff₀ hR).mp hs
  exact min_eq_left hz

end Erdos993Lean.Analytic.V213
