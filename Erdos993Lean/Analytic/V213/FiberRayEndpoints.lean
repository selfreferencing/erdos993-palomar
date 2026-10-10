module

public import Erdos993Lean.Analytic.V213.FiberRayBeta
public import Erdos993Lean.Analytic.V213.FiberRayGuards

/-!
Actual square-root endpoint coefficients and full real-width
transport of the four Eq93 records. The integer certificate values are
used only through their proved canonical shapes and root comparisons.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_ray_endpoint_root_bounds {N R s v : ℝ}
    (hN : 10 ≤ N) (hR : 0 ≤ R) (hRh : R ≤ 1 / 2)
    (hs : Real.sqrt N ≤ s) (hv : (Real.sqrt (cCoef N))⁻¹ ≤ v) :
    fiberRayRhoLower N R v ≤ rhoStar N R ∧
      kappaA N R ≤ fiberRayKappaUpper N R v ∧
      fiberRayE2 N R (R * Real.sqrt N) ≤ fiberRayErrorUpper N R s := by
  have hn : 0 < N := by linarith only [hN]
  have hn1 : 0 < N + 1 := by linarith only [hN]
  have ho := fiberRayCalc_activity_denominator_pos hR hRh
  have hc := fiberRayCalc_cCoef_pos (by linarith only [hN] : 1 < N)
  have hsc := Real.sqrt_pos.mpr hc
  have hsN := Real.sq_sqrt hn.le
  have hsc0 := Real.sqrt_nonneg (cCoef N)
  have hcoef : 0 ≤ 2 / (N + 1) + R ^ 2 / (3 * (1 - R ^ 2)) := by positivity
  have hmult := mul_le_mul_of_nonneg_left hv hcoef
  have hid : rhoStar N R = (1 - R ^ 2) * N / (N + 1) -
      (2 / (N + 1) + R ^ 2 / (3 * (1 - R ^ 2))) * (Real.sqrt (cCoef N))⁻¹ := by
    unfold rhoStar rho
    field_simp [hn1.ne',ho.ne',hsc.ne']
    ring
  constructor
  · rw [hid]
    unfold fiberRayRhoLower
    linarith only [hmult]
  constructor
  · have hkcoef : 0 ≤ 2 * (N + 1) / (3 * N * (1 - R ^ 2)) := by positivity
    have hmk := mul_le_mul_of_nonneg_left hv hkcoef
    have hki : kappaA N R = 2 + (2 * (N + 1) / (3 * N * (1 - R ^ 2))) *
        (Real.sqrt (cCoef N))⁻¹ := by
      unfold kappaA
      field_simp [hn.ne',ho.ne',hsc.ne'] <;> ring
    rw [hki]
    unfold fiberRayKappaUpper
    convert add_le_add_left hmk 2 using 1 <;> ring
  · have hEi : fiberRayE2 N R (R * Real.sqrt N) = fiberRayErrorUpper N R (Real.sqrt N) := by
      rw [fiber_ray_E2_formula]
      unfold fiberRayErrorUpper
      have hs3 : (Real.sqrt N) ^ 3 = N * Real.sqrt N := by
        rw [pow_succ,hsN]
      rw [mul_pow,mul_pow,hsN,hs3]
      field_simp [hn.ne',ho.ne']
      ring
    rw [hEi]
    have hm1 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 5 * R / (6 * (1 - R ^ 2)))
    have hm2 := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ R ^ 3 * N / (12 * (1 - R ^ 2) ^ 2))
    unfold fiberRayErrorUpper
    have hpart1 : 5 * R * Real.sqrt N / (6 * (1 - R ^ 2)) ≤ 5 * R * s / (6 * (1 - R ^ 2)) := by
      convert hm1 using 1 <;> ring
    have hpart2 : ((N + 1) * R ^ 2 + R ^ 3 * N * Real.sqrt N) / (12 * (1 - R ^ 2) ^ 2) ≤
        ((N + 1) * R ^ 2 + R ^ 3 * N * s) / (12 * (1 - R ^ 2) ^ 2) := by
      rw [add_div,add_div]
      apply add_le_add (le_refl _)
      convert hm2 using 1 <;> ring
    linarith only [hpart1,hpart2]

/-- The four literal Eq93 records hold for every real N>=m_f+2. -/
theorem fiber_ray_records_all_real (id : FiberRayIdentity) {N : ℝ}
    (hN : lowMeanFractionReal (fiberRayById id).m_f + 2 ≤ N) :
    let row := fiberRayById id
    let R := lowMeanFractionReal row.R
    let rf := lowMeanFractionReal row.rho_f
    let kf := lowMeanFractionReal row.k_f
    let bf := lowMeanFractionReal row.beta_f
    let df := lowMeanFractionReal row.d_f
    rf ≤ rhoStar N R ∧ 0 < rf ∧ kappaA N R ≤ kf ∧
      bf ≤ fiberRayCappedBeta R N ∧ 0 < bf ∧ 4 ≤ df * rf ^ 2 * bf := by
  have hg := fiber_ray_record_guards id
  have hgap := fiber_ray_record_gaps id
  have hroot := fiber_ray_record_roots id
  dsimp at hg hgap hroot ⊢
  rcases hg with ⟨hR,hRh,hNf,hNeq,hcap,hrf,hbf,hdf,hs0,hv0,hgap0⟩
  have hNh : lowMeanFractionReal (fiberRayById id).N_f ≤ N := by rwa [hNeq]
  have hN10 := hNf.trans hNh
  have hRh' : lowMeanFractionReal (fiberRayById id).R ≤ 1 / 2 := by linarith only [hRh]
  have he := fiber_ray_endpoint_root_bounds hNf hR.le hRh' hroot.1 hroot.2
  have hρf := hgap.1.le.trans he.1
  have hkf := he.2.1.trans hgap.2.1.le
  have hE0 := fiber_ray_E2_nonneg
    (zeta := lowMeanFractionReal (fiberRayById id).R * Real.sqrt (lowMeanFractionReal (fiberRayById id).N_f))
    (by linarith only [hNf]) hR.le hRh' (by positivity)
  have hρ0 : 0 < rhoStar (lowMeanFractionReal (fiberRayById id).N_f)
      (lowMeanFractionReal (fiberRayById id).R) := hrf.trans_le hρf
  have hEplus0 : 0 ≤ fiberRayErrorUpper (lowMeanFractionReal (fiberRayById id).N_f)
      (lowMeanFractionReal (fiberRayById id).R) (lowMeanFractionReal (fiberRayById id).s) := hE0.trans he.2.2
  have hbetaf : lowMeanFractionReal (fiberRayById id).beta_f ≤
      fiberRayCappedBeta (lowMeanFractionReal (fiberRayById id).R)
        (lowMeanFractionReal (fiberRayById id).N_f) := by
    unfold fiberRayCappedBeta
    rw [fiber_ray_cap_pre hR hcap,fiber_ray_beta_formula]
    have hdiv : 2 * fiberRayE2 (lowMeanFractionReal (fiberRayById id).N_f)
        (lowMeanFractionReal (fiberRayById id).R) (lowMeanFractionReal (fiberRayById id).R *
          Real.sqrt (lowMeanFractionReal (fiberRayById id).N_f)) /
        rhoStar (lowMeanFractionReal (fiberRayById id).N_f) (lowMeanFractionReal (fiberRayById id).R) ≤
        2 * fiberRayErrorUpper (lowMeanFractionReal (fiberRayById id).N_f)
          (lowMeanFractionReal (fiberRayById id).R) (lowMeanFractionReal (fiberRayById id).s) /
          lowMeanFractionReal (fiberRayById id).rho_f := by
      calc
        _ ≤ _ / rhoStar (lowMeanFractionReal (fiberRayById id).N_f) (lowMeanFractionReal (fiberRayById id).R) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he.2.2 (by norm_num)) hρ0.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hrf hρf
    have hbud : 2 * fiberRayErrorUpper (lowMeanFractionReal (fiberRayById id).N_f)
        (lowMeanFractionReal (fiberRayById id).R) (lowMeanFractionReal (fiberRayById id).s) /
        lowMeanFractionReal (fiberRayById id).rho_f <
        lowMeanFractionReal (fiberRayById id).N_f - 1 - lowMeanFractionReal (fiberRayById id).beta_f :=
      (div_lt_iff₀ hrf).2 (by nlinarith only [hgap.2.2.1])
    linarith only [hdiv,hbud]
  rcases fiber_upper_coefficient_monotonicity hR.le hRh' with ⟨hkap,_,_,_,_,hρ⟩
  exact ⟨hρf.trans (hρ hNf hN10 hNh),hrf,(hkap hNf hN10 hNh).trans hkf,
    hbetaf.trans (fiber_ray_capped_beta_monotone hR.le hRh hNf hN10 hNh),hbf,hgap.2.2.2.le⟩

end Erdos993Lean.Analytic.V213
