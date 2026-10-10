module

public import Erdos993Lean.Analytic.V213.FiberUpperConsumer
public import Erdos993Lean.Analytic.V213.FiberUpperEndpointStart

/-!
Literal Lemma6.12, with the actual natural-fiber N=M+2 and every
integer rank. The full upper-offset/t>=3/5 result and both t>=1 clauses
are proved. Endpoint sup/start/cutoff hypotheses, all coefficients and
log-ratio comparisons are discharged, including both target signs.
No finite family, numerical test or Section5 theorem remains a premise.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_upper_endpoint_target {t : ℝ} (ht : 0 < t) :
    fiberEndpointTarget 10 (9 / 2) t = fiberPsi t / t := by
  unfold fiberEndpointTarget fiberPsi
  field_simp [ht.ne']
  ring

theorem fiber_upper_endpoint_cap {t : ℝ} (ht : 0 < t) :
    fiberEndpointTarget 10 (9 / 2) t ≤ 1 := by
  have he : fiberEndpointTarget 10 (9 / 2) t = 1 - (9 / 2 : ℝ) * (t - 1) ^ 2 / t := by
    unfold fiberEndpointTarget
    field_simp [ht.ne']
    ring
  rw [he]
  have hh : 0 ≤ (9 / 2 : ℝ) * (t - 1) ^ 2 / t := by positivity
  linarith

theorem fiber_upper_endpoint_envelope {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) {t : ℝ} (ht : 3 / 5 ≤ t) :
    max (fiberEndpointTarget 10 (9 / 2) t) (((N - 2) / N) * fiberEndpointTarget 10 (9 / 2) t) ≤
      fiberEndpointUpper (fiberGainD (N + 1)) (V22.Delta r N) (V22.rhoU r N) t := by
  have hn : 0 < N := by linarith
  have hD := fiber_upper_start_D_bounds (by linarith : 11 ≤ N + 1)
  have hR : 0 < V22.rhoU r N := lt_trans (by norm_num) (fiber_uniform_upper_rate hN hr0 hrh)
  have hd := delta_nonneg (by linarith : 1 ≤ N) (by nlinarith : r ^ 2 < 1)
  have he0 : 0 < (N - 2) / N := div_pos (by linarith) hn
  have he1 : (N - 2) / N ≤ 1 := (div_le_one hn).2 (by linarith)
  have hstar : fiberEndpointStart (fiberGainD (N + 1)) ^ 2 ≤ (1 : ℝ) := by
    have hs : fiberEndpointStart (fiberGainD (N + 1)) ≤ 1 := by
      unfold fiberEndpointStart
      apply Real.exp_le_one_iff.mpr
      linarith [hD.1]
    have hs0 := (fiber_endpoint_start_pos (fiberGainD (N + 1))).le
    nlinarith
  have hcap : sSup ((fiberEndpointTarget 10 (9 / 2)) '' Ioi 0) ≤ 1 + V22.Delta r N := by
    apply csSup_le
    · exact ⟨fiberEndpointTarget 10 (9 / 2) 1, 1, by norm_num, rfl⟩
    · rintro b ⟨x, hx, rfl⟩
      exact (fiber_upper_endpoint_cap hx).trans (by linarith)
  have hstart : max (fiberEndpointTarget 10 (9 / 2) (3 / 5))
      (((N - 2) / N) * fiberEndpointTarget 10 (9 / 2) (3 / 5)) ≤
      fiberEndpointUpper (fiberGainD (N + 1)) (V22.Delta r N) (V22.rhoU r N) (3 / 5) := by
    norm_num only [fiberEndpointTarget]
    rw [max_eq_right (by nlinarith [he1])]
    convert fiber_upper_endpoint_start hN hr0 hrh using 1 <;> ring
  exact fiber_endpoint_principle hD.1 hR hd he0 he1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num only at ⊢; exact hstar) hcap hstart t ht

theorem fiber_upper_gain_D {N r : ℝ} (hN : 10 ≤ N) (hr0 : 0 ≤ r)
    (hrh : r ≤ 1 / 2) : fiberGainD (N + 1) ≤ V22.phiR r N := by
  have hc := fiber_gain_C_half_lower (by linarith : 11 ≤ N + 1)
  have hp := fiber_uniform_phi_lower hN hr0 hrh (le_refl (1 / 2 : ℝ))
  have hm : 0 ≤ r ^ 2 * fiberGainC (1 / 2) (N + 1) := mul_nonneg (sq_nonneg r) (by linarith)
  linarith

theorem fiber_upper_envelope_actual {M : ℕ} (hM : 8 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    fiberEndpointUpper (fiberGainD ((M : ℝ) + 3)) (V22.Delta (fiberSkew q) ((M : ℝ) + 2))
      (V22.rhoU (fiberSkew q) ((M : ℝ) + 2)) ((M : ℝ) / mu) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 10 ≤ M + 2)
  have hR : 0 < V22.rhoU (fiberSkew q) ((M : ℝ) + 2) :=
    lt_trans (by norm_num) (fiber_uniform_upper_rate hN hr0 hrh)
  have ho := fiber_actual_upper_omega_gain (r := fiberSkew q) hmu hM
  have hD := fiber_upper_gain_D hN hr0 hrh
  have hL : fiberEndpointLambda (fiberGainD ((M : ℝ) + 3)) ((M : ℝ) / mu) ≤
      fiberUpperOmega mu (fiberSkew q) (M + 2) := by
    unfold fiberEndpointLambda
    rw [show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] at hD
    linarith
  have hmin := min_le_min_left (0 : ℝ) hL
  have hG := shared_G_antitoneOn_nonpos (min_le_left _ _) (min_le_left _ _) hmin
  have hh := mul_le_mul_of_nonneg_left hG (by positivity : 0 ≤ 2 / V22.rhoU (fiberSkew q) ((M : ℝ) + 2))
  have hF := fiber_upper_constrained_gain hM hq0 hqh hmu j hw
  rw [← fiber_upper_gamma_identity hq0' hq1 M] at hF
  unfold V22.gamma at hF
  unfold fiberEndpointUpper
  linarith

theorem fiber_universal_upper_comparison {M : ℕ} (hM : 8 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j) (ht : 3 / 5 ≤ (M : ℝ) / mu) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hN : (10 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 10 ≤ M + 2)
  have ht0 : 0 < (M : ℝ) / mu := by linarith
  have henv := fiber_upper_endpoint_envelope hN hr0 hrh ht
  rw [show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] at henv
  have hact := fiber_upper_envelope_actual hM hq0 hqh hmu j hw
  have hs := ((le_max_right _ _).trans henv).trans hact
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hmul := (le_div_iff₀ hB).mp hs
  rw [fiber_upper_endpoint_target ht0] at hmul
  have hi : (((M : ℝ) + 2) - 2) / ((M : ℝ) + 2) *
      (fiberPsi ((M : ℝ) / mu) / ((M : ℝ) / mu)) * (((M : ℝ) + 2) / mu) =
      fiberPsi ((M : ℝ) / mu) := by
    have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
    field_simp [hM0.ne', hmu.ne', (by positivity : (M : ℝ) + 2 ≠ 0)]
    ring
  rw [hi] at hmul
  exact hmul

theorem fiber_upper_large_ratio {M : ℕ} (hM : 8 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberBonus q M ≤ fiberSquareOffset q M j) (ht : 1 ≤ (M : ℝ) / mu) :
    (((M : ℝ) + 2) / mu) * fiberBonus q M ≤ fiberF q mu M j := by
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hlog : 0 ≤ Real.log ((M : ℝ) / mu) := Real.log_nonneg ht
  have ho := fiber_uniform_upper_omega_strict hmu hM hr0 hrh
  have hO : 0 ≤ fiberUpperOmega mu (fiberSkew q) (M + 2) := by linarith
  have hh := fiber_upper_constrained_gain hM hq0 hqh hmu j hw
  rw [min_eq_left hO, shared_G_zero] at hh
  simp only [mul_zero, sub_zero] at hh
  convert (le_div_iff₀ (by positivity : 0 < ((M : ℝ) + 2) / mu)).mp hh using 1 <;> ring

theorem fiber_upper_large_ratio_all_nonneg {M : ℕ} (hM : 8 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (ht : 1 ≤ (M : ℝ) / mu) : 0 ≤ fiberF q mu M j := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
  · exact fiber_lower_offset_nonneg hq0' hq1 hmu M j hw
  · have hu := fiber_upper_large_ratio hM hq0 hqh hmu j (le_of_lt (lt_of_not_ge hw)) ht
    have hg : 0 ≤ fiberBonus q M := by
      rw [← fiber_upper_gamma_identity hq0' hq1 M]
      have hd := delta_nonneg (by have hmn := Nat.cast_nonneg (α := ℝ) M; linarith : 1 ≤ (M : ℝ) + 2)
        (by nlinarith [fiber_variance_pos hq0' hq1, fiber_variance_skew q] : fiberSkew q ^ 2 < 1)
      unfold V22.gamma
      linarith
    exact (mul_nonneg (by positivity) hg).trans hu

/-- Literal Lemma6.12 with N=M+2 and its two additional t>=1 clauses. -/
theorem fiber_universal_upper_comparison_skew {M : ℕ} (hM : 8 ≤ M) {r mu : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hmu : 0 < mu) (j : ℤ) :
    (fiberBonus ((1 + r) / 2) M ≤ fiberSquareOffset ((1 + r) / 2) M j →
      3 / 5 ≤ (M : ℝ) / mu → fiberPsi ((M : ℝ) / mu) ≤ fiberF ((1 + r) / 2) mu M j) ∧
    (1 ≤ (M : ℝ) / mu →
      (fiberBonus ((1 + r) / 2) M ≤ fiberSquareOffset ((1 + r) / 2) M j →
        (((M : ℝ) + 2) / mu) * fiberBonus ((1 + r) / 2) M ≤ fiberF ((1 + r) / 2) mu M j) ∧
      0 ≤ fiberF ((1 + r) / 2) mu M j) := by
  have hq0 : (1 / 2 : ℝ) ≤ (1 + r) / 2 := by linarith
  have hqh : (1 + r) / 2 ≤ (3 / 4 : ℝ) := by linarith
  exact ⟨fun hw ht => fiber_universal_upper_comparison hM hq0 hqh hmu j hw ht,
    fun ht => ⟨fun hw => fiber_upper_large_ratio hM hq0 hqh hmu j hw ht,
      fiber_upper_large_ratio_all_nonneg hM hq0 hqh hmu j ht⟩⟩

end Erdos993Lean.Analytic.V213
