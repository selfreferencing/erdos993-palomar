module

public import Erdos993Lean.Analytic.V213.FiberOuterUniversalCheck
public import Erdos993Lean.Analytic.V213.FiberOuterStartPropagation

/-!
Universal upper-offset region: the actual rate, bonus and gain
bounds on every real N>=26 and closed skew interval [1/4,1/2]. The
printed endpoint constants are bound to the accepted F05 singleton;
no sampled width or numerical parameter premise replaces a theorem.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_outer_universal_bonus {N r : ℝ} (hN : 26 ≤ N)
    (hr0 : 1 / 4 ≤ r) (hrh : r ≤ 1 / 2) : (5 / 3 : ℝ) ≤ V22.Delta r N := by
  have hn : 0 < N := by linarith only [hN]
  have hr : 0 ≤ r := by linarith only [hr0]
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hr,hrh]
  have hratio : (1 / 15 : ℝ) ≤ r ^ 2 / (1 - r ^ 2) := by
    apply (le_div_iff₀ ha).2
    nlinarith only [hr0]
  have hterm : (25 : ℝ) ≤ N - 1 + 1 / N := by
    have hi : 0 ≤ 1 / N := by positivity
    linarith only [hN,hi]
  have hm := mul_le_mul hratio hterm (by norm_num : (0 : ℝ) ≤ 25)
    (by positivity : 0 ≤ r ^ 2 / (1 - r ^ 2))
  rw [← fiber_outer_delta_actual hn hr hrh]
  unfold fiberOuterDelta
  norm_num at hm
  simpa only [one_div] using hm

theorem fiber_outer_universal_gain {N r : ℝ} (hN : 26 ≤ N)
    (hr0 : 1 / 4 ≤ r) (hrh : r ≤ 1 / 2) : (2 / 5 : ℝ) < V22.phiR r N := by
  have hr : 0 ≤ r := by linarith only [hr0]
  have hm : 11 ≤ N + 1 := by linarith only [hN]
  have hC := fiber_gain_C_lower hr hrh hm
  have hC0 : 0 ≤ fiberGainC (1 / 2) (N + 1) :=
    (by norm_num : (0 : ℝ) ≤ 769 / 891).trans (fiber_gain_C_half_lower hm)
  have hr2 : (1 / 16 : ℝ) ≤ r ^ 2 := by nlinarith only [hr0]
  have hprod := mul_le_mul hr2 hC hC0 (sq_nonneg r)
  have hmono := (fiber_gain_frozen_strictMono (a := (1 / 4 : ℝ)) (b := (1 / 2 : ℝ))
    (m0 := (27 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).monotoneOn
    (show (27 : ℝ) ∈ Ici 27 from le_rfl) (show N + 1 ∈ Ici 27 by change 27 ≤ N + 1; linarith only [hN])
    (by linarith only [hN] : 27 ≤ N + 1)
  have hstart : fiberGainD 27 + (1 / 4 : ℝ) ^ 2 * fiberGainC (1 / 2) 27 =
      lowMeanFractionReal fiberOuterUniversal.phi_at_start := by
    norm_num [fiberGainD,fiberGainC,fiberOuterUniversal,lowMeanFractionReal]
  have hp := fiber_outer_universal_phi_scalar
  change (2 / 5 : ℝ) < lowMeanFractionReal fiberOuterUniversal.phi_at_start at hp
  have hPhi := fiber_uniform_phi_lower (by linarith only [hN] : 10 ≤ N) hr (le_refl r) hrh
  rw [hstart] at hmono
  nlinarith only [hp,hmono,hprod,hPhi]

theorem fiber_outer_universal_parameters {N r : ℝ} (hN : 26 ≤ N)
    (hr0 : 1 / 4 ≤ r) (hrh : r ≤ 1 / 2) :
    (1 / 3 : ℝ) < V22.rhoU r N ∧ (5 / 3 : ℝ) ≤ V22.Delta r N ∧
      (2 / 5 : ℝ) < V22.phiR r N := by
  exact ⟨fiber_uniform_upper_rate (by linarith only [hN]) (by linarith only [hr0]) hrh,
    fiber_outer_universal_bonus hN hr0 hrh,fiber_outer_universal_gain hN hr0 hrh⟩

end Erdos993Lean.Analytic.V213
