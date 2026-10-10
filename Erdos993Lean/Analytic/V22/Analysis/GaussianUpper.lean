module

public import Erdos993Lean.Analytic.V22.Analysis.InteriorKL
public import Erdos993Lean.Analytic.V22.Analysis.GaussianExponents

/-!
# Section 4: the actual binomial Gaussian upper comparison

Source: the note (version 5), Lemma 4.2(c) and Lemma 4.3(c).
The binomial tilt identity and symmetric upper bound retain every integer
index, including both exterior zero tails. No coefficient-bound premise is
added to either final source comparison.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

noncomputable def sharedGaussianYU (r N : ℝ) : ℝ :=
  Erdos993Lean.Analytic.V22.aHat r * (N + 1) / 2

noncomputable def sharedGaussianY (r : ℝ) (N : ℕ) (J : ℤ) : ℝ :=
  (J : ℝ) - ((1 + r) / 2 * ((N : ℝ) + 1) - 1 / 2)

noncomputable def sharedGaussianU (r : ℝ) (N : ℕ) (J : ℤ) : ℝ :=
  (J : ℝ) - (1 + r) / 2 * ((N : ℝ) - 1) - 1 / 2

noncomputable def sharedGaussianX (r : ℝ) (N : ℕ) (J : ℤ) : ℝ :=
  sharedGaussianU r N J / Erdos993Lean.Analytic.V22.sN r N

noncomputable def sharedGaussianUpperAmplitude (r : ℝ) (N : ℕ) : ℝ :=
  symmetricUpperPrefactor N * (1 - r ^ 2) ^ ((N : ℝ) / 2) *
    Real.exp (((N : ℝ) + 1) * (Erdos993Lean.Analytic.V22.artanh r) ^ 2 / 2)

theorem sharedGaussianYU_nonneg {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    0 ≤ sharedGaussianYU r N := by
  unfold sharedGaussianYU
  exact div_nonneg (mul_nonneg (sharedAHat_bounds hr0 hr1).1 (by linarith)) (by norm_num)

theorem sharedGaussianY_sub_YU (r : ℝ) (N : ℕ) (J : ℤ) :
    sharedGaussianY r N J - sharedGaussianYU r N =
      (J : ℝ) - (N : ℝ) / 2 - Erdos993Lean.Analytic.V22.artanh r * ((N : ℝ) + 1) / 2 := by
  unfold sharedGaussianY sharedGaussianYU Erdos993Lean.Analytic.V22.aHat
  ring

theorem sharedGaussianY_sub_YU_eq_U (r : ℝ) (N : ℕ) (J : ℤ) :
    sharedGaussianY r N J - sharedGaussianYU r N =
      sharedGaussianU r N J - Erdos993Lean.Analytic.V22.yTilde r N := by
  unfold sharedGaussianY sharedGaussianYU sharedGaussianU Erdos993Lean.Analytic.V22.yTilde
  ring

theorem sharedGaussianUpperAmplitude_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    0 < sharedGaussianUpperAmplitude r N := by
  unfold sharedGaussianUpperAmplitude
  exact mul_pos (mul_pos (symmetricUpperPrefactor_pos N)
    (Real.rpow_pos_of_pos (shared_one_sub_sq_pos (by linarith) hr1) _)) (Real.exp_pos _)

/-- Note Lemma 4.2(c), for every integer atom with its original tilt. -/
theorem binomial_gaussian_upper {N : ℕ} (hN : 2 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ) :
    binom N ((1 + r) / 2) J ≤ sharedGaussianUpperAmplitude r N *
      Real.exp (-2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1)) := by
  have hnr : 0 < (N : ℝ) + 1 := by positivity
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hc : 0 ≤ (1 - r ^ 2) ^ ((N : ℝ) / 2) *
      Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) := by
    exact (mul_pos (Real.rpow_pos_of_pos hv _) (Real.exp_pos _)).le
  have hcomp : 2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2) +
        (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1)) =
      ((N : ℝ) + 1) * (Erdos993Lean.Analytic.V22.artanh r) ^ 2 / 2 +
        (-2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1)) := by
    rw [sharedGaussianY_sub_YU]
    field_simp [hnr.ne']
    ring
  rw [binomial_tilt_identity hN hr0 hr1 J]
  calc
    (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
        binom N (1 / 2) J ≤
      (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
        (symmetricUpperPrefactor N * Real.exp (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left (symmetric_binomial_upper hN J) hc
    _ = symmetricUpperPrefactor N * (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        (Real.exp (2 * Erdos993Lean.Analytic.V22.artanh r * ((J : ℝ) - (N : ℝ) / 2)) *
          Real.exp (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1))) := by ring
    _ = sharedGaussianUpperAmplitude r N *
        Real.exp (-2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1)) := by
      rw [← Real.exp_add, hcomp, Real.exp_add]
      unfold sharedGaussianUpperAmplitude
      ring

theorem sharedGaussian_amplitude_normalization {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    Real.sqrt (1 - r ^ 2) * (1 - r ^ 2) ^ ((N : ℝ) / 2) *
        Real.exp (((N : ℝ) + 1) * (Erdos993Lean.Analytic.V22.artanh r) ^ 2 / 2) =
      Real.exp (((N : ℝ) + 1) * Erdos993Lean.Analytic.V22.cr r) := by
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hv, Real.rpow_def_of_pos hv, ← Real.exp_add]
  congr 1
  unfold Erdos993Lean.Analytic.V22.cr
  ring

/-- Note Lemma 4.3(c), expressed in the actual standardized integer offset. -/
theorem binomial_gaussian_upper_normalized {N : ℕ} (hN : 2 ≤ N) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (J : ℤ) :
    Real.sqrt (1 - r ^ 2) / interiorCentralPrefactor N * binom N ((1 + r) / 2) J ≤
      symmetricUpperPrefactor N / interiorCentralPrefactor N * Real.exp
        (((N : ℝ) + 1) * Erdos993Lean.Analytic.V22.cr r - Erdos993Lean.Analytic.V22.c0Prime r N -
          (1 - r ^ 2) * Erdos993Lean.Analytic.V22.rho N / 2 * (sharedGaussianX r N J) ^ 2 +
          Erdos993Lean.Analytic.V22.epsilonPrime r N * |sharedGaussianX r N J|) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hv := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs : 0 < Erdos993Lean.Analytic.V22.sN r N :=
    Real.sqrt_pos.2 (mul_pos (shared_varianceR_pos hr0 hr1) hn)
  have hX : Erdos993Lean.Analytic.V22.sN r N * sharedGaussianX r N J = sharedGaussianU r N J := by
    unfold sharedGaussianX
    field_simp [hs.ne']
  have hquad := shared_upper_exponent_identity hr0 hr1 hn (sharedGaussianX r N J)
  rw [hX, ← sharedGaussianY_sub_YU_eq_U] at hquad
  have heps := shared_epsilonPrime_nonneg hr0 hr1 hn
  have hlin : Erdos993Lean.Analytic.V22.epsilonPrime r N * sharedGaussianX r N J ≤
      Erdos993Lean.Analytic.V22.epsilonPrime r N * |sharedGaussianX r N J| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) heps
  have h := mul_le_mul_of_nonneg_left (binomial_gaussian_upper hN hr0 hr1 J)
    (div_pos (Real.sqrt_pos.2 hv) (interiorCentralPrefactor_pos N)).le
  have heq : Real.sqrt (1 - r ^ 2) / interiorCentralPrefactor N *
      (sharedGaussianUpperAmplitude r N *
        Real.exp (-2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1))) =
      symmetricUpperPrefactor N / interiorCentralPrefactor N * Real.exp
        (((N : ℝ) + 1) * Erdos993Lean.Analytic.V22.cr r -
          2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1)) := by
    unfold sharedGaussianUpperAmplitude
    calc
      _ = symmetricUpperPrefactor N / interiorCentralPrefactor N *
          (Real.sqrt (1 - r ^ 2) * (1 - r ^ 2) ^ ((N : ℝ) / 2) *
            Real.exp (((N : ℝ) + 1) * (Erdos993Lean.Analytic.V22.artanh r) ^ 2 / 2)) *
          Real.exp (-2 * (sharedGaussianY r N J - sharedGaussianYU r N) ^ 2 / ((N : ℝ) + 1)) := by ring
      _ = _ := by
        rw [sharedGaussian_amplitude_normalization hr0 hr1 N, mul_assoc, ← Real.exp_add]
        congr 2
        ring
  rw [heq] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (div_pos (symmetricUpperPrefactor_pos N)
    (interiorCentralPrefactor_pos N)).le
  apply Real.exp_le_exp.mpr
  linarith

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianYU
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianYU
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianU
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianU
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianX
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianX
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianUpperAmplitude
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianUpperAmplitude
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianYU_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianYU_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY_sub_YU
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY_sub_YU
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY_sub_YU_eq_U
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianY_sub_YU_eq_U
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianUpperAmplitude_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianUpperAmplitude_pos
#check Erdos993Lean.Analytic.V22.Analysis.binomial_gaussian_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.binomial_gaussian_upper
#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussian_amplitude_normalization
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussian_amplitude_normalization
#check Erdos993Lean.Analytic.V22.Analysis.binomial_gaussian_upper_normalized
#print axioms Erdos993Lean.Analytic.V22.Analysis.binomial_gaussian_upper_normalized
