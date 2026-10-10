module

public import Erdos993Lean.Analytic.V213.FiberRayCheck

/-!
Semantic consequences of the accepted named F08 kernel checks.
All four strict gaps and both root bounds are bound to the canonical
Eq93 formulas, rather than inferred from unrelated positive roots.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_ray_record_guards (id : FiberRayIdentity) :
    let row := fiberRayById id
    let R := lowMeanFractionReal row.R
    let N := lowMeanFractionReal row.N_f
    let rf := lowMeanFractionReal row.rho_f
    let bf := lowMeanFractionReal row.beta_f
    0 < R ∧ R ≤ 7 / 20 ∧ 10 ≤ N ∧ N = lowMeanFractionReal row.m_f + 2 ∧
      N ≤ (6 / R) ^ 2 ∧ 0 < rf ∧ 0 < bf ∧ 0 < lowMeanFractionReal row.d_f ∧
      0 ≤ lowMeanFractionReal row.s ∧ 0 ≤ lowMeanFractionReal row.v ∧
      0 < lowMeanFractionReal row.minimum_gap := by
  cases id <;> norm_num [fiberRayById,lowMeanFractionReal]

theorem fiber_ray_record_gaps (id : FiberRayIdentity) :
    let row := fiberRayById id
    let N := lowMeanFractionReal row.N_f
    let R := lowMeanFractionReal row.R
    let rf := lowMeanFractionReal row.rho_f
    let kf := lowMeanFractionReal row.k_f
    let bf := lowMeanFractionReal row.beta_f
    let df := lowMeanFractionReal row.d_f
    rf < fiberRayRhoLower N R (lowMeanFractionReal row.v) ∧
      fiberRayKappaUpper N R (lowMeanFractionReal row.v) < kf ∧
      2 * fiberRayErrorUpper N R (lowMeanFractionReal row.s) < rf * (N - 1 - bf) ∧
      4 < df * rf ^ 2 * bf := by
  have hg := fiber_ray_record_guards id
  have hρ := fiber_ray_gap_checked id .rhoGap (Or.inl rfl)
  have hk := fiber_ray_gap_checked id .kappaGap (Or.inr (Or.inl rfl))
  have hb := fiber_ray_gap_checked id .betaGap (Or.inr (Or.inr (Or.inl rfl)))
  have hd := fiber_ray_gap_checked id .squareGap (Or.inr (Or.inr (Or.inr rfl)))
  dsimp [fiberRayValue] at hρ hk hb hd
  dsimp at hg ⊢
  rcases hg with ⟨hR,hRh,hN,hNeq,hcap,hrf,hbf,hdf,hs0,hv0,hgap⟩
  rw [← hNeq] at hρ hk hb
  constructor
  · linarith only [hρ,hgap]
  constructor
  · linarith only [hk,hgap]
  constructor
  · linarith only [hb,hgap]
  · linarith only [hd,hgap]

theorem fiber_ray_record_roots (id : FiberRayIdentity) :
    let row := fiberRayById id
    let N := lowMeanFractionReal row.N_f
    Real.sqrt N ≤ lowMeanFractionReal row.s ∧
      (Real.sqrt (1 - 1 / N))⁻¹ ≤ lowMeanFractionReal row.v := by
  have hg := fiber_ray_record_guards id
  have hs := fiber_ray_root_checked id .sqrtS (Or.inl rfl)
  have hv := fiber_ray_root_checked id .sqrtV (Or.inr rfl)
  dsimp [fiberRayValue] at hs hv
  dsimp at hg ⊢
  rcases hg with ⟨hR,hRh,hN10,hNeq,hcap,hrf,hbf,hdf,hs0,hv0,hgap⟩
  rw [← hNeq] at hs hv
  have hN : 0 < lowMeanFractionReal (fiberRayById id).N_f := by linarith only [hN10]
  have hc : 0 < 1 - 1 / lowMeanFractionReal (fiberRayById id).N_f := by
    have h := (div_lt_one hN).2 (by linarith only [hN10] : 1 < lowMeanFractionReal (fiberRayById id).N_f)
    linarith only [h]
  have hsc := Real.sqrt_pos.mpr hc
  have hscsq := Real.sq_sqrt hc.le
  constructor
  · exact Real.sqrt_le_iff.mpr ⟨hs0,by linarith only [hs]⟩
  · rw [← one_div]
    apply (div_le_iff₀ hsc).2
    have hvs := mul_nonneg (hv0) hsc.le
    have hid : (lowMeanFractionReal (fiberRayById id).v * Real.sqrt
        (1 - 1 / lowMeanFractionReal (fiberRayById id).N_f)) ^ 2 ≥ 1 := by
      rw [mul_pow,hscsq]
      linarith only [hv]
    nlinarith only [hid,hvs]

end Erdos993Lean.Analytic.V213
