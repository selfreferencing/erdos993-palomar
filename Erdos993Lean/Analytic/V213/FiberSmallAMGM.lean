module

public import Erdos993Lean.Analytic.V213.FiberKernel
public import Mathlib.Analysis.MeanInequalities

/-!
The actual repeated-factor AM--GM comparison in Lemma6.20.
Integer multiplicities include
both zero endpoints. This generic analytic proof consumes no finite data.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_small_rpow_power {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : 0 < n)
    (k : ℕ) : (x ^ ((k : ℝ) / n)) ^ n = x ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hn', Real.rpow_natCast]

theorem fiber_small_repeated_amgm {N J : ℕ} (hJ : J ≤ N) {x y z : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ J * y ^ (N - J) * z ≤
      (((J : ℝ) * x + (N - J : ℕ) * y + z) / (N + 1)) ^ (N + 1) := by
  have hm : (0 : ℝ) < N + 1 := by positivity
  have hw : (J : ℝ) / (N + 1) + ((N - J : ℕ) : ℝ) / (N + 1) +
      1 / (N + 1) = 1 := by
    rw [Nat.cast_sub hJ]
    field_simp
    ring
  have h := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (J : ℝ) / (N + 1)) (w₂ := ((N - J : ℕ) : ℝ) / (N + 1))
    (w₃ := 1 / (N + 1)) (by positivity) (by positivity) (by positivity) hx hy hz hw
  have hp := pow_le_pow_left₀ (by positivity :
    (0 : ℝ) ≤ x ^ ((J : ℝ) / (N + 1)) *
      y ^ (((N - J : ℕ) : ℝ) / (N + 1)) * z ^ ((1 : ℝ) / (N + 1))) h (N + 1)
  have hx' := fiber_small_rpow_power hx (by omega : 0 < N + 1) J
  have hy' := fiber_small_rpow_power hy (by omega : 0 < N + 1) (N - J)
  have hz' := fiber_small_rpow_power hz (by omega : 0 < N + 1) 1
  push_cast at hx' hy' hz'
  rw [mul_pow, mul_pow, hx', hy', hz', pow_one] at hp
  convert hp using 1 <;> push_cast <;> ring

noncomputable def fiberSmallT (N J : ℕ) : ℝ :=
  3 * N * ((N : ℝ) - 1) - 4 * J * ((N : ℝ) - J)

noncomputable def fiberSmallFactor (N J : ℕ) (q : ℝ) : ℝ :=
  4 * ((N : ℝ) - 1) * ((N : ℝ) - 2 * J) * q -
    ((N : ℝ) * ((N : ℝ) - 1) - 4 * J * ((J : ℝ) - 1))

noncomputable def fiberSmallU (N J : ℕ) : ℝ :=
  (N.choose J : ℝ) * fiberSmallT N J ^ (N + 1) /
    ((N : ℝ) * ((N : ℝ) - 1) * ((N : ℝ) + 1) ^ (N + 1) *
      (4 * ((N : ℝ) - 1)) ^ N)

theorem fiber_small_factor_sum {N J : ℕ} (hJ : J ≤ N) (q : ℝ) :
    (J : ℝ) * (4 * ((N : ℝ) - 1) * q) +
      (N - J : ℕ) * (4 * ((N : ℝ) - 1) * (1 - q)) + fiberSmallFactor N J q =
      fiberSmallT N J := by
  unfold fiberSmallFactor fiberSmallT
  rw [Nat.cast_sub hJ]
  ring

theorem fiber_small_T_nonneg {N J : ℕ} (hN : 2 ≤ N) (hJ : J ≤ N) :
    0 ≤ fiberSmallT N J := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  unfold fiberSmallT
  nlinarith only [sq_nonneg ((N : ℝ) - 2 * J), hn]

theorem fiber_small_U_nonneg {N J : ℕ} (hN : 2 ≤ N) (hJ : J ≤ N) :
    0 ≤ fiberSmallU N J := by
  have ht := fiber_small_T_nonneg hN hJ
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : (0 : ℝ) ≤ (N : ℝ) - 1 := by linarith
  unfold fiberSmallU
  positivity

end Erdos993Lean.Analytic.V213
