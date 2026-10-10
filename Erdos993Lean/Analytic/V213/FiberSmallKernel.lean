module

public import Erdos993Lean.Analytic.V213.FiberSmallAMGM

/-!
Exact supported-rank kernel identity and all-q AM--GM upper bound
for its negative. Source: Lemma6.20 proof.
The supported binomial index includes J=0 and J=N, hence both spike ranks.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_small_kernel_factor (M J : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    -kernel2 q (fiberWeightL q) (fiberWeightR q) M ((J : ℤ) - 1) =
      ((M + 2).choose J : ℝ) * q ^ J * (1 - q) ^ (M + 2 - J) /
        (((M : ℝ) + 2) * ((M : ℝ) + 1)) * fiberSmallFactor (M + 2) J q := by
  rw [fiber_kernel_exact M _ hq0 hq1,
    show (J : ℤ) - 1 + 1 = (J : ℤ) by ring, binom_nat]
  unfold fiberSmallFactor fiberKernelPolynomial fiberOffset fiberSkew
  push_cast
  ring

theorem fiber_small_amgm_bound {N J : ℕ} (hN : 2 ≤ N) (hJ : J ≤ N)
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (N.choose J : ℝ) * q ^ J * (1 - q) ^ (N - J) /
      ((N : ℝ) * ((N : ℝ) - 1)) * fiberSmallFactor N J q ≤ fiberSmallU N J := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) < (N : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < N := by linarith
  have hq' : 0 ≤ 1 - q := sub_nonneg.mpr hq1
  have hU := fiber_small_U_nonneg hN hJ
  by_cases hf : 0 ≤ fiberSmallFactor N J q
  · let A : ℝ := 4 * ((N : ℝ) - 1)
    have hA : 0 < A := by dsimp [A]; positivity
    have hAp : 0 < A ^ N := pow_pos hA N
    have h := fiber_small_repeated_amgm hJ
      (x := A * q) (y := A * (1 - q)) (z := fiberSmallFactor N J q)
      (mul_nonneg hA.le hq0) (mul_nonneg hA.le hq') hf
    have hsum := fiber_small_factor_sum hJ q
    change (J : ℝ) * (A * q) + (N - J : ℕ) * (A * (1 - q)) +
      fiberSmallFactor N J q = fiberSmallT N J at hsum
    rw [hsum] at h
    have hprod : (A * q) ^ J * (A * (1 - q)) ^ (N - J) * fiberSmallFactor N J q =
        A ^ N * (q ^ J * (1 - q) ^ (N - J) * fiberSmallFactor N J q) := by
      simp only [mul_pow]
      calc
        _ = (A ^ J * A ^ (N - J)) *
            (q ^ J * (1 - q) ^ (N - J) * fiberSmallFactor N J q) := by ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hJ]
    rw [hprod] at h
    have hp : q ^ J * (1 - q) ^ (N - J) * fiberSmallFactor N J q ≤
        (fiberSmallT N J / ((N : ℝ) + 1)) ^ (N + 1) / A ^ N := by
      apply (le_div_iff₀ hAp).mpr
      simpa only [mul_comm] using h
    have hc : 0 ≤ (N.choose J : ℝ) / ((N : ℝ) * ((N : ℝ) - 1)) := by positivity
    have hb := mul_le_mul_of_nonneg_left hp hc
    convert hb using 1
    · ring
    · unfold fiberSmallU A
      rw [div_pow]
      field_simp [hn0.ne', hn1.ne', show (N : ℝ) + 1 ≠ 0 by positivity]
  · have hf' : fiberSmallFactor N J q ≤ 0 := (not_le.mp hf).le
    have hc : 0 ≤ (N.choose J : ℝ) * q ^ J * (1 - q) ^ (N - J) /
        ((N : ℝ) * ((N : ℝ) - 1)) := by positivity
    exact (mul_nonpos_of_nonneg_of_nonpos hc hf').trans hU

theorem fiber_small_supported_kernel (M : ℕ) {J : ℕ} (hJ : J ≤ M + 2)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    -kernel2 q (fiberWeightL q) (fiberWeightR q) M ((J : ℤ) - 1) ≤
      fiberSmallU (M + 2) J := by
  rw [fiber_small_kernel_factor M J hq0 hq1]
  have h := fiber_small_amgm_bound (by omega : 2 ≤ M + 2) hJ hq0.le hq1.le
  simpa only [Nat.cast_add, Nat.cast_ofNat, show (M : ℝ) + 2 - 1 = M + 1 by ring] using h

end Erdos993Lean.Analytic.V213
