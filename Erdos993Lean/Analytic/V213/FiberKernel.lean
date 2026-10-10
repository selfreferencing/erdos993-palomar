module

public import Erdos993Lean.Analytic.V213.FiberReflection
public import Erdos993Lean.Analytic.V22.Analysis.Kernel

/-!
Exact normalized kernel formula `r12:eq64`.
The full integer axis includes both adjacent off-support ranks and both tails.
The source quadratic is derived from the accepted binomial/kernel definitions.
No generated finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def fiberKernelPolynomial (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  ((M : ℝ) + 2) + fiberSkew q ^ 2 * ((M : ℝ) + 1) ^ 2 - 4 * fiberOffset q M j ^ 2

noncomputable def fiberSquareOffset (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  fiberOffset q M j ^ 2 / (fiberVariance q * ((M : ℝ) + 2))

noncomputable def fiberBonus (q : ℝ) (M : ℕ) : ℝ :=
  1 + fiberSkew q ^ 2 * (((M : ℝ) + 2) ^ 2 - ((M : ℝ) + 2) + 1) /
    ((1 - fiberSkew q ^ 2) * ((M : ℝ) + 2))

theorem fiber_AG_port_identity :
    fiberAG = Erdos993Lean.Analytic.V22.Analysis.gaussianA := by
  apply Real.log_injOn_pos fiber_AG_pos (by
    change 0 < Erdos993Lean.Analytic.V22.Analysis.gaussianA
    unfold Erdos993Lean.Analytic.V22.Analysis.gaussianA
    positivity)
  unfold fiberAG Erdos993Lean.Analytic.V22.Analysis.gaussianA
  simp (disch := positivity) only [Real.log_inv, Real.log_sqrt,
    Real.log_div, Real.log_mul, Real.log_exp]
  ring

theorem fiber_bonus_port_identity {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    fiberBonus q M = Erdos993Lean.Analytic.V22.Analysis.bonus q M := by
  have hv := fiber_variance_pos hq0 hq1
  have hr : 1 - fiberSkew q ^ 2 ≠ 0 := by rw [fiber_variance_skew]; positivity
  have hm : (M : ℝ) + 2 ≠ 0 := by positivity
  unfold fiberBonus Erdos993Lean.Analytic.V22.Analysis.bonus
  change 1 + fiberSkew q ^ 2 * _ / _ =
    (((M : ℝ) + 2) + fiberSkew q ^ 2 * ((M : ℝ) + 1) ^ 2) /
      ((1 - fiberSkew q ^ 2) * ((M : ℝ) + 2))
  field_simp [hr, hm]
  ring

theorem fiber_choose_double_lift {M n : ℕ} (hn : n ≤ M) :
    ((n : ℝ) + 1) * ((M : ℝ) + 1 - n) * ((M + 2).choose (n + 1) : ℝ) =
      ((M : ℝ) + 2) * ((M : ℝ) + 1) * (M.choose n : ℝ) := by
  have hc1 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_mul_succ_eq M n)
  have hc2 := congrArg (fun x : ℕ => (x : ℝ)) (Nat.add_one_mul_choose_eq (M + 1) n)
  push_cast at hc1 hc2
  rw [Nat.cast_sub (by omega : n ≤ M + 1)] at hc1
  push_cast at hc1
  linear_combination -((M : ℝ) + 1 - n) * hc2 - ((M : ℝ) + 2) * hc1

theorem fiber_binom_double_lift {M n : ℕ} (hn : n ≤ M) (q : ℝ) :
    ((n : ℝ) + 1) * ((M : ℝ) + 1 - n) * binom (M + 2) q ((n + 1 : ℕ) : ℤ) =
      ((M : ℝ) + 2) * ((M : ℝ) + 1) * q * (1 - q) * binom M q (n : ℤ) := by
  have hc := fiber_choose_double_lift hn
  rw [binom_nat, binom_nat, show M + 2 - (n + 1) = M - n + 1 by omega]
  simp only [pow_succ]
  linear_combination (q ^ n * (1 - q) ^ (M - n) * q * (1 - q)) * hc

theorem fiber_kernel_supported {M n : ℕ} (hn : n ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    kernel2 q (fiberWeightL q) (fiberWeightR q) M (n : ℤ) =
      binom (M + 2) q ((n + 1 : ℕ) : ℤ) /
        (((M : ℝ) + 2) * ((M : ℝ) + 1)) * fiberKernelPolynomial q M (n : ℤ) := by
  have h := Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq hq0 hq1 M (n : ℤ)
  simpa [Erdos993Lean.Analytic.V22.Analysis.weightedKernel,
    Erdos993Lean.Analytic.V22.Analysis.weightL, Erdos993Lean.Analytic.V22.Analysis.weightR,
    Erdos993Lean.Analytic.V22.Analysis.signedR, Erdos993Lean.Analytic.V22.Analysis.offset,
    fiberWeightL, fiberWeightR, fiberKernelPolynomial, fiberSkew, fiberOffset,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem fiber_kernel_exact (M : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    kernel2 q (fiberWeightL q) (fiberWeightR q) M j =
      binom (M + 2) q (j + 1) /
        (((M : ℝ) + 2) * ((M : ℝ) + 1)) * fiberKernelPolynomial q M j := by
  have h := Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq hq0 hq1 M j
  simpa [Erdos993Lean.Analytic.V22.Analysis.weightedKernel,
    Erdos993Lean.Analytic.V22.Analysis.weightL, Erdos993Lean.Analytic.V22.Analysis.weightR,
    Erdos993Lean.Analytic.V22.Analysis.signedR, Erdos993Lean.Analytic.V22.Analysis.offset,
    fiberWeightL, fiberWeightR, fiberKernelPolynomial, fiberSkew, fiberOffset,
    div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

theorem fiber_kernel_normalized (M : ℕ) (j : ℤ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    kernel2 q (fiberWeightL q) (fiberWeightR q) M j =
      4 * fiberVariance q * binom (M + 2) q (j + 1) *
        (fiberBonus q M - fiberSquareOffset q M j) / ((M : ℝ) + 1) := by
  rw [fiber_bonus_port_identity hq0 hq1]
  exact Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq_normalized hq0 hq1 M j

theorem fiber_F_normalized (M : ℕ) (j : ℤ) {q mu : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu) :
    fiberF q mu M j =
      mu ^ (3 / 2 : ℝ) * Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) /
        (2 * fiberAG * ((M : ℝ) + 1)) * (fiberBonus q M - fiberSquareOffset q M j) +
      (((M : ℝ) + 2) / mu) * fiberSquareOffset q M j := by
  have hv := fiber_variance_pos hq0 hq1
  have hs : Real.sqrt (fiberVariance q) ^ 2 = fiberVariance q := Real.sq_sqrt hv.le
  have hsp : 0 < Real.sqrt (fiberVariance q) := Real.sqrt_pos.mpr hv
  have hr : Real.sqrt (1 - fiberSkew q ^ 2) = 2 * Real.sqrt (fiberVariance q) := by
    rw [fiber_variance_skew, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  unfold fiberF fiberNormalization
  rw [fiber_kernel_normalized M j hq0 hq1, hr]
  unfold fiberSquareOffset
  have hm1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (M : ℝ) + 2 ≠ 0 := by positivity
  field_simp [fiber_AG_pos.ne', hv.ne', hsp.ne', hmu.ne', hm1, hm2]
  generalize he : Real.sqrt (fiberVariance q) = s
  have hs' : s ^ 2 = fiberVariance q := by simpa [he] using hs
  rw [← hs']
  simp only [Real.rpow_eq_pow]
  ring

end Erdos993Lean.Analytic.V213
