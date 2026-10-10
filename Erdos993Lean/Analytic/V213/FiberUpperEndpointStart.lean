module

public import Erdos993Lean.Analytic.V213.FiberUpperEndpointRate
public import Erdos993Lean.Analytic.V213.FiberNegativeBarrier
public import Erdos993Lean.Analytic.V213.FiberEndpointPrinciple

/-!
The exact closed t=3/5 start test for universal upper comparison6.12.
Log bounds follow accepted positive artanh estimates; the actual root and
Eq80 control G. Both signs of the endpoint target are retained. No finite
transcription family is used and no endpoint inequality is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_upper_start_log_bounds :
    -(23 / 18 : ℝ) ≤ (5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) ∧
      (5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) ≤ -1 := by
  have hb := (sharedAHat_bounds (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).2
  norm_num [V22.aHat, V22.artanh] at hb
  have hi : Real.log (3 / 5 : ℝ) = -Real.log (5 / 3 : ℝ) := by
    rw [show (3 / 5 : ℝ) = (5 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hu := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3 / 5)
  rw [hi] at hu
  rw [hi]
  constructor <;> linarith

theorem fiber_upper_start_G1 : V22.G1 (-(3 / 4 : ℝ)) < -(1 / 2 : ℝ) := by
  have hb := (sharedAHat_bounds (by norm_num : (0 : ℝ) ≤ 1 / 5)
    (by norm_num : (1 / 5 : ℝ) < 1)).2
  norm_num [V22.aHat, V22.artanh] at hb
  have hi : Real.log (2 / 3 : ℝ) = -Real.log (3 / 2 : ℝ) := by
    rw [show (2 / 3 : ℝ) = (3 / 2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have he : -(3 / 4 : ℝ) < rootEquation (-(1 / 3 : ℝ)) := by
    unfold rootEquation
    norm_num only
    rw [hi]
    linarith
  have hs : V22.rootMap (-(3 / 4 : ℝ)) < -(1 / 3 : ℝ) := by
    have hroot : rootMap (rootEquation (-(1 / 3 : ℝ))) = -(1 / 3 : ℝ) :=
      rootMap_eq_of_equation (by norm_num) rfl
    rw [shared_rootMap_eq]
    have h := rootMap_strictMono he
    rw [hroot] at h
    exact h
  have hd : 0 < 1 + V22.rootMap (-(3 / 4 : ℝ)) := by
    linarith [shared_rootMap_gt_neg_one (-(3 / 4 : ℝ))]
  unfold V22.G1
  apply (div_lt_iff₀ hd).2
  linarith

theorem fiber_upper_start_D_bounds {m : ℝ} (hm : 11 ≤ m) :
    0 < fiberGainD m ∧ fiberGainD m < 1 / 4 := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hl := fiber_gain_D_lower hm
  have hp : 0 < (439 : ℝ) / (180 * m) := by positivity
  have he : fiberGainD m = (51 / 20 - 1 / (m - 2)) / m := by
    unfold fiberGainD
    field_simp [hm0.ne', hm2.ne']
    ring
  have hu : fiberGainD m < (51 / 20 : ℝ) / m := by
    rw [he]
    exact div_lt_div_of_pos_right (by have := one_div_pos.mpr hm2; linarith) hm0
  have hu' : (51 / 20 : ℝ) / m ≤ (51 / 220 : ℝ) := by
    apply (div_le_iff₀ hm0).2
    linarith
  exact ⟨hp.trans_le hl, by linarith⟩

theorem fiber_upper_start_root_gain {p : ℝ} (hp0 : 0 ≤ p) (hph : p < 1 / 4) :
    2 * V22.G ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + p) < 6 / 5 - p := by
  have ho := fiber_upper_start_log_bounds
  have hG := shared_G_antitoneOn_nonpos (by norm_num : -(23 / 18 : ℝ) ≤ 0)
    (by linarith : (5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) ≤ 0) ho.1
  have hb := fiber_negative_root_barrier (by norm_num : (0 : ℝ) ≤ 23 / 18)
    (by norm_num : (23 / 18 : ℝ) ≤ 3)
  norm_num at hb
  have h0 : V22.G ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ)) < 3 / 5 := by linarith
  have htop : (5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + p ≤ -(3 / 4 : ℝ) := by linarith
  have h1 := shared_G1_monotone htop
  have h1' : V22.G1 ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + p) ≤ -(1 / 2 : ℝ) :=
    h1.trans fiber_upper_start_G1.le
  have hm := mul_le_mul_of_nonneg_left h1' hp0
  have ht := fiber_G_taylor_all_real ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ)) p
  linarith

theorem fiber_upper_start_margin {N : ℝ} (hN : 10 ≤ N) :
    8 / (5 * (N + 1)) + 144 / (25 * (N + 1) ^ 2) < fiberGainD (N + 1) := by
  have hm : 0 < N + 1 := by linarith
  have hd := fiber_gain_D_lower (by linarith : 11 ≤ N + 1)
  have hh : 144 / (25 * (N + 1)) ≤ (144 / 275 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 25 * (N + 1))).2
    linarith
  have he : (8 / 5 + 144 / (25 * (N + 1))) / (N + 1) =
      8 / (5 * (N + 1)) + 144 / (25 * (N + 1) ^ 2) := by
    field_simp [hm.ne']
  have hlt : 8 / 5 + 144 / (25 * (N + 1)) < (439 / 180 : ℝ) := by linarith
  have h := div_lt_div_of_pos_right hlt hm
  rw [he] at h
  exact h.trans_le (by convert hd using 1 <;> field_simp [hm.ne'])

theorem fiber_upper_endpoint_start {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) :
    -((N - 2) / N) / 5 ≤
      fiberEndpointUpper (fiberGainD (N + 1)) (V22.Delta r N) (V22.rhoU r N) (3 / 5) := by
  have hd := fiber_upper_start_D_bounds (by linarith : 11 ≤ N + 1)
  have hroot := fiber_upper_start_root_gain hd.1.le hd.2
  have hs := fiber_upper_endpoint_square hN hr0 hrh
  have hm := fiber_upper_start_margin hN
  have hR : 0 < V22.rhoU r N := lt_trans (by norm_num) (fiber_uniform_upper_rate hN hr0 hrh)
  have hg : 2 * V22.G ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + fiberGainD (N + 1)) ≤
      (V22.gamma r N + fiberUpperEndpointC N) * V22.rhoU r N := by linarith
  have harg : (5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + fiberGainD (N + 1) ≤ 0 := by
    have hl := fiber_upper_start_log_bounds
    linarith
  unfold fiberEndpointUpper fiberEndpointLambda
  rw [min_eq_right harg]
  have hdiv : 2 / V22.rhoU r N *
      V22.G ((5 / 2 : ℝ) * Real.log (3 / 5 : ℝ) + fiberGainD (N + 1)) ≤
      V22.gamma r N + fiberUpperEndpointC N := by
    convert (div_le_iff₀ hR).2 hg using 1 <;> ring
  unfold V22.gamma fiberUpperEndpointC at hdiv
  have he : (N - 2) / (5 * N) = ((N - 2) / N) / 5 := by ring
  rw [he] at hdiv
  linarith

end Erdos993Lean.Analytic.V213
