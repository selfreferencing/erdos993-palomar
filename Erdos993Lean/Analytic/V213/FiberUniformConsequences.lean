module

public import Erdos993Lean.Analytic.V213.FiberUniformGain

/-!
Further literal Lemma6.10 consequences: strict upper rate and actual
upper log-ratio gain, including the large-activity regime. The rate proof
retains the exact rational bound in the accepted coefficient proof.
No finite DF10 family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_rhoStar_precise_lower {N rm : ℝ} (hN : 10 ≤ N)
    (hrm0 : 0 ≤ rm) (hrmh : rm ≤ 1 / 2) : (635 / 1782 : ℝ) ≤ V22.rhoStar N rm := by
  have hn : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hrmsq : rm ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hd : (3 / 4 : ℝ) ≤ 1 - rm ^ 2 := by linarith
  have hs := linearized_sqrt_cCoef_lower hN
  have hs0 : 0 < Real.sqrt (V22.cCoef N) := by linarith
  have hrho : (10 / 11 : ℝ) ≤ V22.rho N := by
    unfold V22.rho
    apply (le_div_iff₀ hn1).2
    linarith
  have hmain : (15 / 22 : ℝ) ≤ (1 - rm ^ 2) * V22.rho N := by
    have h := mul_le_mul hd hrho (by norm_num : (0 : ℝ) ≤ 10 / 11) (by linarith : 0 ≤ 1 - rm ^ 2)
    norm_num at h ⊢
    exact h
  have hden1 : (99 / 10 : ℝ) ≤ (N + 1) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (show (11 : ℝ) ≤ N + 1 by linarith) hs (by norm_num : (0 : ℝ) ≤ 9 / 10) hn1.le
    norm_num at h
    exact h
  have hterm1 : 2 / ((N + 1) * Real.sqrt (V22.cCoef N)) ≤ (20 / 99 : ℝ) := by
    have h := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) < 99 / 10) hden1
    norm_num at h
    exact h
  have hden2 : (81 / 40 : ℝ) ≤ 3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N) := by
    have h := mul_le_mul (mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 3)) hs
      (by norm_num : (0 : ℝ) ≤ 9 / 10) (by linarith : 0 ≤ 3 * (1 - rm ^ 2))
    norm_num at h
    exact h
  have hterm2 : rm ^ 2 / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) ≤ (10 / 81 : ℝ) := by
    calc
      _ ≤ (1 / 4 : ℝ) / (3 * (1 - rm ^ 2) * Real.sqrt (V22.cCoef N)) :=
        div_le_div_of_nonneg_right hrmsq (by positivity)
      _ ≤ (1 / 4 : ℝ) / (81 / 40) :=
        div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden2
      _ = _ := by norm_num
  unfold V22.rhoStar
  linarith


theorem fiber_uniform_upper_rate {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) : (1 / 3 : ℝ) < V22.rhoU r N := by
  have hs := fiber_rhoStar_precise_lower hN hr0 hrh
  have hU := fiber_upper_rate_lower hN hr0 (le_refl r) hrh
  linarith

theorem fiber_uniform_upper_omega_strict {mu r : ℝ} {M : ℕ}
    (hmu : 0 < mu) (hM : 8 ≤ M) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    5 / 2 * Real.log ((M : ℝ) / mu) < fiberUpperOmega mu r (M + 2) := by
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 10 ≤ M + 2)
  have hp := (fiber_uniform_phi_strict hN hr0 (le_refl r) hrh).2
  have ho := fiber_actual_upper_omega_gain (r := r) hmu hM
  linarith

theorem fiber_gain_C_half_linear {m : ℝ} (hm : 11 ≤ m) :
    m / 3 - 4 ≤ fiberGainC (1 / 2) m := by
  have hm0 : 0 < m := by linarith
  have hm2 : 0 < m - 2 := by linarith
  have hx : 2 / (9 * (m - 2)) ≤ (2 / 81 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 9 * (m - 2))).2
    linarith
  rw [fiber_gain_C_half_formula hm]
  have h8 : 0 ≤ 8 / m := by positivity
  linarith

theorem fiber_uniform_phi_large_activity {r N : ℝ} (hN : 10 ≤ N)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hzeta : 6 ≤ r * Real.sqrt N) :
    (r * Real.sqrt N) ^ 2 / 4 ≤ V22.phiR r N := by
  have hn : 0 ≤ N := by linarith
  have hsq : (r * Real.sqrt N) ^ 2 = r ^ 2 * N := by
    rw [mul_pow, Real.sq_sqrt hn]
  have hzsq : 36 ≤ r ^ 2 * N := by
    rw [← hsq]
    nlinarith
  have hr2 : r ^ 2 ≤ (1 / 4 : ℝ) := by nlinarith
  have hbig : 144 ≤ N := by
    have h := mul_le_mul_of_nonneg_right hr2 hn
    nlinarith
  have hC : N / 4 ≤ fiberGainC r (N + 1) := by
    have h := fiber_gain_C_half_linear (m := N + 1) (by linarith)
    have hb := fiber_gain_C_lower hr0 hrh (m := N + 1) (by linarith)
    linarith
  have hD := fiber_gain_D_lower (m := N + 1) (by linarith)
  have hDpos : 0 < fiberGainD (N + 1) := lt_of_lt_of_le (by positivity) hD
  have hPhi := fiber_uniform_phi_lower hN hr0 (le_refl r) hrh
  have hCp := mul_le_mul_of_nonneg_left hC (sq_nonneg r)
  rw [hsq]
  nlinarith

theorem fiber_large_activity_upper_omega {mu r : ℝ} {M : ℕ}
    (hmu : 0 < mu) (hM : 8 ≤ M) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hzeta : 6 ≤ r * Real.sqrt ((M : ℝ) + 2)) :
    5 / 2 * Real.log ((M : ℝ) / mu) + (r * Real.sqrt ((M : ℝ) + 2)) ^ 2 / 4 ≤
      fiberUpperOmega mu r (M + 2) := by
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 10 ≤ M + 2)
  have hp := fiber_uniform_phi_large_activity hN hr0 hrh hzeta
  have ho := fiber_actual_upper_omega_gain (r := r) hmu hM
  linarith

theorem fiber_exp_two_gt_seven : (7 : ℝ) < Real.exp 2 := by
  have h := Real.sum_le_exp_of_nonneg (x := 2) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem fiber_large_activity_upper_omega_pos {mu r : ℝ} {M : ℕ}
    (hmu : 0 < mu) (hM : 8 ≤ M) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hzeta : 6 ≤ r * Real.sqrt ((M : ℝ) + 2)) (ht : 1 / 7 ≤ (M : ℝ) / mu) :
    0 < fiberUpperOmega mu r (M + 2) := by
  have hlog7 : Real.log 7 < 2 :=
    (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 7)).2 fiber_exp_two_gt_seven
  have htlog := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 7) ht
  rw [one_div, Real.log_inv] at htlog
  have ho := fiber_large_activity_upper_omega hmu hM hr0 hrh hzeta
  nlinarith

end Erdos993Lean.Analytic.V213
