module

public import Erdos993Lean.Analytic.V213.FiberUniformConsequences

/-!
Exact endpoint-rate estimate in the proof of Lemma6.12, on all real
N>=10 and closed skew r in[0,1/2]. The actual gamma/rho_U formulas are
used, with their radius identity. The final completed-square lower bound
retains no algebraic or numerical premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberUpperEndpointC (N : ℝ) : ℝ := (N - 2) / (5 * N)

noncomputable def fiberUpperEndpointK (N : ℝ) : ℝ :=
  (13 * N - 82 - 4 * Real.sqrt N) / 15 + 47 / (5 * (N + 1))

theorem fiber_upper_endpoint_c_bounds {N : ℝ} (hN : 10 ≤ N) :
    0 ≤ fiberUpperEndpointC N ∧ fiberUpperEndpointC N ≤ 1 / 5 := by
  have hn : 0 < N := by linarith
  have hn2 : 0 ≤ N - 2 := by linarith
  unfold fiberUpperEndpointC
  constructor
  · positivity
  · apply (div_le_iff₀ (by positivity : 0 < 5 * N)).2
    linarith

theorem fiber_upper_endpoint_radius {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r) :
    fiberUpperRadius r N ≤ Real.sqrt N + r * (N - 1) := by
  have hn : 0 < N := by linarith
  have hs := Real.sq_sqrt hn.le
  have hS := Real.sq_sqrt (by positivity : 0 ≤ N + r ^ 2 * (N - 1) ^ 2)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by
    have hrn : 0 ≤ r * (N - 1) := mul_nonneg hr0 (by linarith)
    positivity)).1
  nlinarith [mul_nonneg (Real.sqrt_nonneg N) (mul_nonneg hr0 (by linarith : 0 ≤ N - 1))]

theorem fiber_upper_endpoint_aHat {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 ≤ V22.aHat r ∧ V22.aHat r ≤ 4 * r ^ 3 / 9 := by
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have hb := sharedAHat_bounds hr0 (by linarith : r < 1)
  constructor
  · exact hb.1
  · apply hb.2.trans
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 3) ha)).2
    have hp := mul_nonneg (pow_nonneg hr0 3) (by nlinarith : 0 ≤ 1 / 4 - r ^ 2)
    nlinarith

theorem fiber_upper_endpoint_epsilon {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) :
    V22.epsilonPrime r N ≤ (2 * r / (N + 1) + V22.aHat r) * Real.sqrt N := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have he : 2 * V22.sN r N = Real.sqrt ((1 - r ^ 2) * N) := by
    have hs := shared_sN_sq hr0 (by linarith : r < 1) hn
    have ht := Real.sq_sqrt (mul_pos ha hn).le
    have hS : 0 ≤ V22.sN r N := by unfold V22.sN; exact Real.sqrt_nonneg _
    apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).1
    unfold V22.varianceR at hs
    nlinarith
  have heps : V22.epsilonPrime r N =
      (2 * r / (N + 1) + V22.aHat r) * Real.sqrt ((1 - r ^ 2) * N) := by
    unfold V22.epsilonPrime V22.yTilde
    rw [← he]
    field_simp [hm.ne']
    ring
  rw [heps]
  apply mul_le_mul_of_nonneg_left _ (by
    have ha0 := (fiber_upper_endpoint_aHat hr0 hrh).1
    positivity)
  exact Real.sqrt_le_sqrt (by nlinarith [mul_nonneg (sq_nonneg r) hn.le])

theorem fiber_upper_endpoint_rate {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) :
    6 / 5 - 8 / (5 * (N + 1)) + fiberUpperEndpointK N * r ^ 2 -
      12 * r * Real.sqrt N / (5 * (N + 1)) ≤
        (V22.gamma r N + fiberUpperEndpointC N) * V22.rhoU r N := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hr1 : r < 1 := by linarith
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  have hc := fiber_upper_endpoint_c_bounds hN
  have heps := shared_epsilonPrime_nonneg hr0 hr1 hn
  have hD := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : r ^ 2 < 1)
  have hg : 1 ≤ V22.gamma r N := by unfold V22.gamma; linarith
  have hg0 : 0 < V22.gamma r N := by linarith
  have hgs : 1 ≤ Real.sqrt (V22.gamma r N) := by
    apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) hg0.le).2
    simpa using hg
  have hgsq := Real.sq_sqrt hg0.le
  have hgs0 := Real.sqrt_pos.2 hg0
  have hgr : V22.gamma r N * V22.rhoU r N =
      fiberUpperRadius r N ^ 2 / (N + 1) - V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) := by
    have ht : V22.gamma r N / Real.sqrt (V22.gamma r N) = Real.sqrt (V22.gamma r N) := by
      field_simp [hgs0.ne']
      exact hgsq.symm
    have hgR : V22.gamma r N * (1 - r ^ 2) * N = fiberUpperRadius r N ^ 2 := by
      rw [fiber_gamma_radius hr0 hr1 (by linarith)]
      field_simp [ha.ne', hn.ne']
    unfold V22.rhoU V22.rho
    calc
      _ = (V22.gamma r N * (1 - r ^ 2) * N) / (N + 1) -
        V22.epsilonPrime r N * (V22.gamma r N / Real.sqrt (V22.gamma r N)) := by ring
      _ = _ := by rw [hgR, ht]
  have hdiv : V22.epsilonPrime r N / Real.sqrt (V22.gamma r N) ≤ V22.epsilonPrime r N := by
    apply (div_le_iff₀ hgs0).2
    nlinarith
  have hcr : fiberUpperEndpointC N * ((1 - r ^ 2) * N / (N + 1) - V22.epsilonPrime r N) ≤
      fiberUpperEndpointC N * V22.rhoU r N := by
    apply mul_le_mul_of_nonneg_left _ hc.1
    unfold V22.rhoU V22.rho
    have hnorm : (1 - r ^ 2) * (N / (N + 1)) = (1 - r ^ 2) * N / (N + 1) := by ring
    rw [hnorm]
    linarith
  have hepsR := fiber_epsilon_radius hr0 hr1 (by linarith : 1 < N)
  have hepsU := fiber_upper_endpoint_epsilon hN hr0 hrh
  have hA := fiber_upper_endpoint_aHat hr0 hrh
  have hS := fiber_upper_endpoint_radius hN hr0
  have hS0 := (fiberUpperRadius_pos (r := r) hn).le
  have hfirst : (N + r ^ 2 * (N - 1) ^ 2 + (N - 2) * (1 - r ^ 2) / 5) / (N + 1) -
      (2 * r / (N + 1) + V22.aHat r) *
        (fiberUpperRadius r N + fiberUpperEndpointC N * Real.sqrt N) ≤
      (V22.gamma r N + fiberUpperEndpointC N) * V22.rhoU r N := by
    have hcu := mul_le_mul_of_nonneg_left hepsU hc.1
    have heq : fiberUpperEndpointC N * ((1 - r ^ 2) * N / (N + 1)) =
        (N - 2) * (1 - r ^ 2) / (5 * (N + 1)) := by
      unfold fiberUpperEndpointC
      field_simp [hn.ne', hm.ne']
    have heq' : V22.epsilonPrime r N * Real.sqrt (V22.gamma r N) =
        (2 * r / (N + 1) + V22.aHat r) * fiberUpperRadius r N := by
      rw [hepsR]
      unfold V22.yTilde
      field_simp [hm.ne']
    have hSq : fiberUpperRadius r N ^ 2 = N + r ^ 2 * (N - 1) ^ 2 :=
      Real.sq_sqrt (by positivity)
    rw [hSq, heq'] at hgr
    rw [mul_sub, heq] at hcr
    have heqL : (N + r ^ 2 * (N - 1) ^ 2 + (N - 2) * (1 - r ^ 2) / 5) / (N + 1) -
        (2 * r / (N + 1) + V22.aHat r) *
          (fiberUpperRadius r N + fiberUpperEndpointC N * Real.sqrt N) =
        (N + r ^ 2 * (N - 1) ^ 2) / (N + 1) -
          (2 * r / (N + 1) + V22.aHat r) * fiberUpperRadius r N +
          ((N - 2) * (1 - r ^ 2) / (5 * (N + 1)) -
            fiberUpperEndpointC N * ((2 * r / (N + 1) + V22.aHat r) * Real.sqrt N)) := by
      field_simp [hm.ne']
      ring
    rw [heqL]
    nlinarith only [hgr, hcr, hcu]
  have hprod : (2 * r / (N + 1) + V22.aHat r) *
      (fiberUpperRadius r N + fiberUpperEndpointC N * Real.sqrt N) ≤
      (2 * r / (N + 1) + 4 * r ^ 3 / 9) * (6 * Real.sqrt N / 5 + r * (N - 1)) := by
    have hcS := mul_le_mul_of_nonneg_right hc.2 (Real.sqrt_nonneg N)
    have hc0 := hc.1
    have ha0 := hA.1
    have hn1 : 0 ≤ N - 1 := by linarith
    exact mul_le_mul (by linarith only [hA.2]) (by linarith only [hS, hcS])
      (add_nonneg hS0 (mul_nonneg hc0 (Real.sqrt_nonneg N))) (by positivity)
  have hweak : (N + r ^ 2 * (N - 1) ^ 2 + (N - 2) * (1 - r ^ 2) / 5) / (N + 1) -
      (2 * r / (N + 1) + 4 * r ^ 3 / 9) * (6 * Real.sqrt N / 5 + r * (N - 1)) ≤
      (V22.gamma r N + fiberUpperEndpointC N) * V22.rhoU r N := by linarith
  have h3 : r ^ 3 ≤ r ^ 2 / 2 := by nlinarith [mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrh)]
  have h4 : r ^ 4 ≤ r ^ 2 / 4 := by nlinarith [mul_nonneg (sq_nonneg r) (by nlinarith : 0 ≤ 1 / 4 - r ^ 2)]
  have h3s := mul_le_mul_of_nonneg_right h3 (by positivity : 0 ≤ 8 * Real.sqrt N / 15)
  have h4s := mul_le_mul_of_nonneg_right h4 (by linarith : 0 ≤ 4 * (N - 1) / 9)
  have hiden : (N + r ^ 2 * (N - 1) ^ 2 + (N - 2) * (1 - r ^ 2) / 5) / (N + 1) -
      (12 * r * Real.sqrt N / (5 * (N + 1)) + 2 * r ^ 2 * (N - 1) / (N + 1) +
        4 * r ^ 2 * Real.sqrt N / 15 + r ^ 2 * (N - 1) / 9) -
      (6 / 5 - 8 / (5 * (N + 1)) + fiberUpperEndpointK N * r ^ 2 -
        12 * r * Real.sqrt N / (5 * (N + 1))) =
      r ^ 2 * (N - 1) * (N + 19) / (45 * (N + 1)) := by
    unfold fiberUpperEndpointK
    field_simp [hm.ne']
    ring
  have hn1 : 0 ≤ N - 1 := by linarith
  have hsur : 0 ≤ r ^ 2 * (N - 1) * (N + 19) / (45 * (N + 1)) := by positivity
  have hexpand : (2 * r / (N + 1) + 4 * r ^ 3 / 9) *
      (6 * Real.sqrt N / 5 + r * (N - 1)) =
      12 * r * Real.sqrt N / (5 * (N + 1)) + 2 * r ^ 2 * (N - 1) / (N + 1) +
        8 * r ^ 3 * Real.sqrt N / 15 + 4 * r ^ 4 * (N - 1) / 9 := by
    field_simp [hm.ne']
    ring
  rw [hexpand] at hweak
  nlinarith only [hweak, h3s, h4s, hiden, hsur]

theorem fiber_upper_endpoint_K {N : ℝ} (hN : 10 ≤ N) : N / 4 < fiberUpperEndpointK N := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hs : Real.sqrt N ≤ N / 2 := by
    apply (Real.sqrt_le_iff).2
    exact ⟨by linarith, by nlinarith⟩
  have hy : 0 ≤ N - 10 := by linarith
  have hp : 0 < (29 * (N - 10) ^ 2 + 281 * (N - 10) + 146) / (60 * (N + 1)) := by positivity
  have hi : ((13 * N - 82 - 4 * (N / 2)) / 15 + 47 / (5 * (N + 1))) - N / 4 =
      (29 * (N - 10) ^ 2 + 281 * (N - 10) + 146) / (60 * (N + 1)) := by
    field_simp [hm.ne']
    ring
  unfold fiberUpperEndpointK
  linarith

theorem fiber_upper_endpoint_square {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) :
    6 / 5 - 8 / (5 * (N + 1)) - 144 / (25 * (N + 1) ^ 2) ≤
      (V22.gamma r N + fiberUpperEndpointC N) * V22.rhoU r N := by
  have hk := fiber_upper_endpoint_K hN
  have hks := mul_le_mul_of_nonneg_right hk.le (sq_nonneg r)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ N)
  have hsq := sq_nonneg (Real.sqrt N * r / 2 - 12 / (5 * (N + 1)))
  have hm : 0 < N + 1 := by linarith
  have hclear : N / 4 * r ^ 2 - 12 * r * Real.sqrt N / (5 * (N + 1)) +
      144 / (25 * (N + 1) ^ 2) ≥ 0 := by
    have hi : N / 4 * r ^ 2 - 12 * r * Real.sqrt N / (5 * (N + 1)) +
        144 / (25 * (N + 1) ^ 2) =
        (Real.sqrt N * r / 2 - 12 / (5 * (N + 1))) ^ 2 := by
      field_simp [hm.ne']
      ring_nf
      rw [hs]
      ring
    rw [hi]
    exact hsq
  linarith [fiber_upper_endpoint_rate hN hr0 hrh]

end Erdos993Lean.Analytic.V213
