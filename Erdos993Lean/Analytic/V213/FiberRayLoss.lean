module

public import Erdos993Lean.Analytic.V213.FiberRayEndpoints

/-!
Separate actual reciprocal, variance-bonus and combined exponent
loss bounds. The completed-square maximum uses the literal positive
rho_f/beta_f record, and does not discard the separate N Delta bonus.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_E2_zeta_monotone {N R x y : ℝ}
    (hN : 0 < N) (hR : 0 ≤ R) (hRh : R ≤ 1 / 2) (hx : 0 ≤ x) (hxy : x ≤ y) :
    fiberRayE2 N R x ≤ fiberRayE2 N R y := by
  have ho := fiberRayCalc_activity_denominator_pos hR hRh
  unfold fiberRayE2 e2 e3 e4 e5
  gcongr

theorem fiber_ray_quadratic_loss_max {rho beta zeta : ℝ} (hr : 0 < rho) (hb : 0 < beta) :
    4 * zeta / rho - beta * zeta ^ 2 ≤ 4 / (rho ^ 2 * beta) := by
  apply (le_div_iff₀ (by positivity : 0 < rho ^ 2 * beta)).2
  have hsq := sq_nonneg (rho * beta * zeta - 2)
  have hid : (4 * zeta / rho - beta * zeta ^ 2) * (rho ^ 2 * beta) =
      4 - (rho * beta * zeta - 2) ^ 2 := by
    field_simp [hr.ne']
    ring
  rw [hid]
  linarith only [hsq]

theorem fiber_ray_combined_loss_bound (id : FiberRayIdentity) {N r : ℝ}
    (hN : lowMeanFractionReal (fiberRayById id).m_f + 2 ≤ N)
    (hr : 0 ≤ r) (hrR : r ≤ lowMeanFractionReal (fiberRayById id).R)
    (hz : r * Real.sqrt N ≤ 6) :
    2 * N * eU r N / rhoU r N - N * Delta r N ≤
      lowMeanFractionReal (fiberRayById id).d_f := by
  have hg := fiber_ray_record_guards id
  have hc := fiber_ray_records_all_real id hN
  dsimp at hg hc
  rcases hg with ⟨hR,hRh,hNf,hNeq,hcap,hrf,hbf,hdf,hs0,hv0,hgap0⟩
  have hN10 : 10 ≤ N := hNf.trans (by rwa [hNeq])
  have hRp : lowMeanFractionReal (fiberRayById id).R ≤ 1 / 2 := by linarith only [hRh]
  have hrp : r ≤ 1 / 2 := hrR.trans hRp
  have hρ := fiber_upper_rate_lower hN10 hr hrR hRp
  have hρs : 0 < rhoStar N (lowMeanFractionReal (fiberRayById id).R) := hc.2.1.trans_le hc.1
  have hρU := hρs.trans_le hρ
  have hζ0 : 0 ≤ r * Real.sqrt N := by positivity
  have hζcap : r * Real.sqrt N ≤ fiberRayZeta (lowMeanFractionReal (fiberRayById id).R) N := by
    exact le_min hz (mul_le_mul_of_nonneg_right hrR (Real.sqrt_nonneg N))
  have hE2 := fiber_ray_E2_zeta_monotone (by linarith only [hN10]) hR.le hRp hζ0 hζcap
  have hexp := fiber_upper_exponent_loss hN10 hr hrR hRp
  have hEi : 2 * (r * Real.sqrt N) + (r * Real.sqrt N) ^ 2 / 2 +
      5 * (r * Real.sqrt N) ^ 3 / (6 * (1 - lowMeanFractionReal (fiberRayById id).R ^ 2)) +
      (N + 1) * (r * Real.sqrt N) ^ 4 / (12 * N * (1 - lowMeanFractionReal (fiberRayById id).R ^ 2) ^ 2) +
      (r * Real.sqrt N) ^ 5 / (12 * (1 - lowMeanFractionReal (fiberRayById id).R ^ 2) ^ 2) =
      2 * (r * Real.sqrt N) + fiberRayE2 N (lowMeanFractionReal (fiberRayById id).R)
        (r * Real.sqrt N) * (r * Real.sqrt N) ^ 2 := by
    rw [fiber_ray_E2_formula]
    ring
  rw [hEi] at hexp
  have hEz : N * eU r N ≤ 2 * (r * Real.sqrt N) +
      fiberRayE2 N (lowMeanFractionReal (fiberRayById id).R)
        (fiberRayZeta (lowMeanFractionReal (fiberRayById id).R) N) * (r * Real.sqrt N) ^ 2 := by
    exact hexp.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hE2 (sq_nonneg _)))
  have hEcap0 := fiber_ray_E2_nonneg (by linarith only [hN10]) hR.le hRp (hζ0.trans hζcap)
  have hnum0 : 0 ≤ 2 * (2 * (r * Real.sqrt N) +
      fiberRayE2 N (lowMeanFractionReal (fiberRayById id).R)
        (fiberRayZeta (lowMeanFractionReal (fiberRayById id).R) N) * (r * Real.sqrt N) ^ 2) := by positivity
  have hdiv : 2 * N * eU r N / rhoU r N ≤
      2 * (2 * (r * Real.sqrt N) +
        fiberRayE2 N (lowMeanFractionReal (fiberRayById id).R)
          (fiberRayZeta (lowMeanFractionReal (fiberRayById id).R) N) * (r * Real.sqrt N) ^ 2) /
        rhoStar N (lowMeanFractionReal (fiberRayById id).R) := by
    calc
      _ ≤ _ / rhoU r N := by
        apply div_le_div_of_nonneg_right _ hρU.le
        nlinarith only [hEz]
      _ ≤ _ := div_le_div_of_nonneg_left hnum0 hρs hρ
  have hbonus := fiber_activity_bonus hN10 hr hrp
  have hid : 2 * (2 * (r * Real.sqrt N) +
      fiberRayE2 N (lowMeanFractionReal (fiberRayById id).R)
        (fiberRayZeta (lowMeanFractionReal (fiberRayById id).R) N) * (r * Real.sqrt N) ^ 2) /
        rhoStar N (lowMeanFractionReal (fiberRayById id).R) - (N - 1) * (r * Real.sqrt N) ^ 2 =
      4 * (r * Real.sqrt N) / rhoStar N (lowMeanFractionReal (fiberRayById id).R) -
        fiberRayCappedBeta (lowMeanFractionReal (fiberRayById id).R) N * (r * Real.sqrt N) ^ 2 := by
    unfold fiberRayCappedBeta fiberRayBeta
    ring
  have hρf : 4 * (r * Real.sqrt N) / rhoStar N (lowMeanFractionReal (fiberRayById id).R) ≤
      4 * (r * Real.sqrt N) / lowMeanFractionReal (fiberRayById id).rho_f :=
    div_le_div_of_nonneg_left (by positivity) hrf hc.1
  have hβf := mul_le_mul_of_nonneg_right hc.2.2.2.1 (sq_nonneg (r * Real.sqrt N))
  have hquad := fiber_ray_quadratic_loss_max hrf hbf (zeta := r * Real.sqrt N)
  have hdf : 4 / (lowMeanFractionReal (fiberRayById id).rho_f ^ 2 *
      lowMeanFractionReal (fiberRayById id).beta_f) ≤ lowMeanFractionReal (fiberRayById id).d_f := by
    apply (div_le_iff₀ (by positivity)).2
    convert hc.2.2.2.2.2 using 1 <;> ring
  have hfin := hquad.trans hdf
  linarith only [hdiv,hbonus,hid,hρf,hβf,hfin]

end Erdos993Lean.Analytic.V213
