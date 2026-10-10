module

public import Erdos993Lean.Analytic.V22.Analysis.GaussianCalculus

/-!
# Section 4: exact standardized exponent identities

Source: the note (version 5), Lemma 4.3(a) and its preceding
definitions. The parameter `x` is the actual standardized offset, so
`u=s_N*x` and `w=x^2`. No sign restriction is imposed on the offset.
These algebraic identities hold for every positive real `N`, hence include
the note's integer range.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set

noncomputable def sharedGaussianZ (r N u : ℝ) : ℝ := 2 * (u - r) / (N + 1)

theorem shared_varianceR_pos {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < Erdos993Lean.Analytic.V22.varianceR r := by
  unfold Erdos993Lean.Analytic.V22.varianceR
  exact div_pos (shared_one_sub_sq_pos (by linarith) hr1) (by norm_num)

theorem shared_sN_sq {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    (Erdos993Lean.Analytic.V22.sN r N) ^ 2 = Erdos993Lean.Analytic.V22.varianceR r * N := by
  exact Real.sq_sqrt (mul_pos (shared_varianceR_pos hr0 hr1) hN).le

theorem shared_epsilon_eq {r N : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    Erdos993Lean.Analytic.V22.epsilon r N =
      r * Erdos993Lean.Analytic.V22.sN r N /
        (Erdos993Lean.Analytic.V22.varianceR r * (N + 1)) := by
  have hv := shared_varianceR_pos hr0 hr1
  have hs : 0 < Real.sqrt (Erdos993Lean.Analytic.V22.varianceR r) := Real.sqrt_pos.2 hv
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have he : Erdos993Lean.Analytic.V22.varianceR r * (N + 1) =
      Real.sqrt (Erdos993Lean.Analytic.V22.varianceR r) *
        (Real.sqrt (Erdos993Lean.Analytic.V22.varianceR r) * (N + 1)) := by
    rw [← mul_assoc, ← pow_two, Real.sq_sqrt hv.le]
  unfold Erdos993Lean.Analytic.V22.epsilon Erdos993Lean.Analytic.V22.sN
  rw [Real.sqrt_mul hv.le N, he]
  field_simp [hs.ne', hn1] <;> ring

/-- Source Lemma 4.3(a), first exact exponent, in its standardized coordinate. -/
theorem shared_lower_exponent_identity {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) (x : ℝ) :
    (N + 1) * (sharedGaussianZ r N (Erdos993Lean.Analytic.V22.sN r N * x)) ^ 2 /
        (2 * (1 - r ^ 2)) =
      Erdos993Lean.Analytic.V22.rho N / 2 * x ^ 2 -
        Erdos993Lean.Analytic.V22.epsilon r N * x + Erdos993Lean.Analytic.V22.c0 r N := by
  have hv := shared_varianceR_pos hr0 hr1
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have hs := shared_sN_sq hr0 hr1 hN
  have hvr : 1 - r ^ 2 = 4 * Erdos993Lean.Analytic.V22.varianceR r := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    ring
  rw [shared_epsilon_eq hr0 hr1 hN, hvr]
  unfold sharedGaussianZ Erdos993Lean.Analytic.V22.rho Erdos993Lean.Analytic.V22.c0
  field_simp [hv.ne', hn1]
  ring_nf
  rw [hs]
  ring

/-- Source Lemma 4.3(a), second exact exponent; `u-yTilde=y-y_U`. -/
theorem shared_upper_exponent_identity {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) (x : ℝ) :
    2 * (Erdos993Lean.Analytic.V22.sN r N * x - Erdos993Lean.Analytic.V22.yTilde r N) ^ 2 / (N + 1) =
      (1 - r ^ 2) * Erdos993Lean.Analytic.V22.rho N / 2 * x ^ 2 -
        Erdos993Lean.Analytic.V22.epsilonPrime r N * x + Erdos993Lean.Analytic.V22.c0Prime r N := by
  have hn1 : N + 1 ≠ 0 := ne_of_gt (by linarith)
  have hs := shared_sN_sq hr0 hr1 hN
  unfold Erdos993Lean.Analytic.V22.rho Erdos993Lean.Analytic.V22.epsilonPrime
    Erdos993Lean.Analytic.V22.c0Prime
  field_simp [hn1]
  ring_nf
  rw [hs]
  unfold Erdos993Lean.Analytic.V22.varianceR
  ring

theorem shared_sN_le_half_sqrt {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) :
    Erdos993Lean.Analytic.V22.sN r N ≤ Real.sqrt N / 2 := by
  have hs := shared_sN_sq hr0 hr1 hN
  have hn := Real.sq_sqrt hN.le
  have hs0 : 0 ≤ Erdos993Lean.Analytic.V22.sN r N := Real.sqrt_nonneg _
  have hn0 := Real.sqrt_nonneg N
  have hv : Erdos993Lean.Analytic.V22.varianceR r ≤ (1 / 4 : ℝ) := by
    unfold Erdos993Lean.Analytic.V22.varianceR
    nlinarith [sq_nonneg r]
  have hb := mul_le_mul_of_nonneg_right hv hN.le
  nlinarith

/-- The source's original width-one windows lie in the domains of both
Gaussian bounds; no unproved numerical decimal estimate is used. -/
theorem shared_gaussian_window_domains {r N : ℝ}
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hN : 10 ≤ N) :
    0 < Erdos993Lean.Analytic.V22.ZL r N 1 ∧ Erdos993Lean.Analytic.V22.ZL r N 1 < 1 ∧
      0 < Erdos993Lean.Analytic.V22.ZR r N 1 ∧ r + Erdos993Lean.Analytic.V22.ZR r N 1 < 1 := by
  have hr1 : r < 1 := by linarith
  have hn0 : 0 < N := by linarith
  have hn1 : 0 < N + 1 := by linarith
  have hs0 : 0 < Erdos993Lean.Analytic.V22.sN r N := Real.sqrt_pos.2
    (mul_pos (shared_varianceR_pos hr0 hr1) hn0)
  have hs := shared_sN_le_half_sqrt hr0 hr1 hn0
  have hnroot := Real.sq_sqrt hn0.le
  have hnroot0 := Real.sqrt_nonneg N
  have hroot : Real.sqrt N < N := by nlinarith
  have hroot2 : 2 * Real.sqrt N < N + 1 := by nlinarith
  unfold Erdos993Lean.Analytic.V22.ZL Erdos993Lean.Analytic.V22.ZR
  norm_num only [Real.sqrt_one, one_mul]
  refine ⟨div_pos (by linarith) hn1, ?_, div_pos (by linarith) hn1, ?_⟩
  · apply (div_lt_one hn1).2
    linarith
  · have hright : 2 * Erdos993Lean.Analytic.V22.sN r N / (N + 1) < 1 / 2 := by
      apply (div_lt_iff₀ hn1).2
      linarith
    linarith

theorem shared_epsilon_nonneg {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) : 0 ≤ Erdos993Lean.Analytic.V22.epsilon r N := by
  rw [shared_epsilon_eq hr0 hr1 hN]
  exact div_nonneg (mul_nonneg hr0 (Real.sqrt_nonneg _))
    (mul_pos (shared_varianceR_pos hr0 hr1) (by linarith : 0 < N + 1)).le

theorem shared_yTilde_nonneg {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) : 0 ≤ Erdos993Lean.Analytic.V22.yTilde r N := by
  unfold Erdos993Lean.Analytic.V22.yTilde
  exact add_nonneg hr0 (div_nonneg (mul_nonneg (sharedAHat_bounds hr0 hr1).1
    (by linarith : 0 ≤ N + 1)) (by norm_num))

theorem shared_epsilonPrime_nonneg {r N : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hN : 0 < N) : 0 ≤ Erdos993Lean.Analytic.V22.epsilonPrime r N := by
  unfold Erdos993Lean.Analytic.V22.epsilonPrime
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (shared_yTilde_nonneg hr0 hr1 hN))
    (Real.sqrt_nonneg _)) (by linarith)

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.sharedGaussianZ
#print axioms Erdos993Lean.Analytic.V22.Analysis.sharedGaussianZ
#check Erdos993Lean.Analytic.V22.Analysis.shared_varianceR_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_varianceR_pos
#check Erdos993Lean.Analytic.V22.Analysis.shared_sN_sq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_sN_sq
#check Erdos993Lean.Analytic.V22.Analysis.shared_epsilon_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_epsilon_eq
#check Erdos993Lean.Analytic.V22.Analysis.shared_lower_exponent_identity
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_lower_exponent_identity
#check Erdos993Lean.Analytic.V22.Analysis.shared_upper_exponent_identity
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_upper_exponent_identity
#check Erdos993Lean.Analytic.V22.Analysis.shared_sN_le_half_sqrt
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_sN_le_half_sqrt
#check Erdos993Lean.Analytic.V22.Analysis.shared_gaussian_window_domains
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_gaussian_window_domains
#check Erdos993Lean.Analytic.V22.Analysis.shared_epsilon_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_epsilon_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.shared_yTilde_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_yTilde_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.shared_epsilonPrime_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.shared_epsilonPrime_nonneg
