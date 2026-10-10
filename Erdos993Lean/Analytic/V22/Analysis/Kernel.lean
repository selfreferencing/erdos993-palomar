module

public import Erdos993Lean.Analytic.MGF.Criterion
public import Erdos993Lean.Analytic.NoValley.Binom

/-!
# Version 2.2 of the manuscript: the weighted binomial kernel

Source: the fiber theorem note, Section 2.2 and Lemma 3.1.
All integer indices are retained, including both boundary spikes and indices
outside the support. This module does not select or reconstruct forest data.
Consumer: the note's fiber function and Proposition 2.1 (the MGF criterion).
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Erdos993Lean.Analytic.NoValley

/-- Source: note Section 2.2, the left weight. -/
def weightL (q : ℝ) : ℝ := q ^ 2 * (3 - 4 * q)

/-- Source: note Section 2.2, the right weight. -/
def weightR (q : ℝ) : ℝ := (1 - q) ^ 2 * (4 * q - 1)

/-- Source: note Section 2.2, the signed activity displacement. -/
def signedR (q : ℝ) : ℝ := 2 * q - 1

/-- Source: note Section 2.2, the variance per trial. -/
def variance (q : ℝ) : ℝ := q * (1 - q)

/-- Source: note Section 2.2, the shifted offset `u = δ - r/2`. -/
noncomputable def offset (q : ℝ) (M : ℕ) (j : ℤ) : ℝ := (j : ℝ) - q * M - signedR q / 2

/-- Source: note Section 2.2, the standardized squared offset. -/
noncomputable def squareOffset (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  offset q M j ^ 2 / (variance q * ((M : ℝ) + 2))

/-- Source: note Section 2.2, the bonus factor `γ`. -/
noncomputable def bonus (q : ℝ) (M : ℕ) : ℝ :=
  (((M : ℝ) + 2) + signedR q ^ 2 * ((M : ℝ) + 1) ^ 2) /
    ((1 - signedR q ^ 2) * ((M : ℝ) + 2))

/-- Source: note Section 2.2, the weighted kernel `κ_w`. -/
noncomputable def weightedKernel (q : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  kernel2 q (weightL q) (weightR q) M j

/-- Source: note Section 2.2, nonnegative weights on the full stated interval. -/
theorem weights_nonneg {q : ℝ} (hqa : 1 / 4 ≤ q) (hqb : q ≤ 3 / 4) :
    0 ≤ weightL q ∧ 0 ≤ weightR q := by
  constructor
  · exact mul_nonneg (sq_nonneg q) (by linarith)
  · exact mul_nonneg (sq_nonneg (1 - q)) (by linarith)

/-- Source: note Section 2.2, `1-r² = 4v`. -/
theorem one_sub_signedR_sq (q : ℝ) : 1 - signedR q ^ 2 = 4 * variance q := by
  unfold signedR variance
  ring

/-- Source: note Section 2.2, `u = J-q(N-1)-1/2`. -/
theorem offset_eq (q : ℝ) (M : ℕ) (j : ℤ) :
    offset q M j = ((j : ℝ) + 1) - q * ((M : ℝ) + 1) - 1 / 2 := by
  unfold offset signedR
  ring

/-- Source: note Lemma 3.1, the polynomial calculation before division. -/
theorem weightedKernel_mul (q : ℝ) (M : ℕ) (j : ℤ)
    (_hq0 : q ≠ 0) (_hq1 : 1 - q ≠ 0) :
    (((M : ℝ) + 2) * ((M : ℝ) + 1)) * weightedKernel q M j =
      binom (M + 2) q (j + 1) *
        (((M : ℝ) + 2) + signedR q ^ 2 * ((M : ℝ) + 1) ^ 2 - 4 * offset q M j ^ 2) := by
  have hm := binom_two_step_mid M q j
  have hl := binom_two_step_left M q j
  have hr := binom_two_step_right M q j
  have hk : weightedKernel q M j =
      2 * (q * (1 - q)) * binom M q j -
        (3 - 4 * q) * q ^ 2 * binom M q (j - 1) -
        (4 * q - 1) * (1 - q) ^ 2 * binom M q (j + 1) := by
    unfold weightedKernel kernel2 weightL weightR fL fR
    field_simp
    ring
  rw [hk]
  unfold offset signedR
  linear_combination 2 * hm - (3 - 4 * q) * hl - (4 * q - 1) * hr

/-- Source: note Lemma 3.1, first form, for every integer index. -/
theorem weightedKernel_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) (j : ℤ) :
    weightedKernel q M j =
      binom (M + 2) q (j + 1) *
        (((M : ℝ) + 2) + signedR q ^ 2 * ((M : ℝ) + 1) ^ 2 - 4 * offset q M j ^ 2) /
      (((M : ℝ) + 2) * ((M : ℝ) + 1)) := by
  have hd : ((M : ℝ) + 2) * ((M : ℝ) + 1) ≠ 0 := by positivity
  apply (eq_div_iff hd).2
  simpa [mul_comm] using weightedKernel_mul q M j hq0.ne' (by linarith)

/-- Source: note Lemma 3.1, second form `4v B_N(J)(γ-w)/(N-1)`. -/
theorem weightedKernel_eq_normalized {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) :
    weightedKernel q M j =
      4 * variance q * binom (M + 2) q (j + 1) * (bonus q M - squareOffset q M j) /
        ((M : ℝ) + 1) := by
  rw [weightedKernel_eq hq0 hq1]
  unfold bonus squareOffset
  rw [one_sub_signedR_sq]
  have hv : variance q ≠ 0 := mul_ne_zero hq0.ne' (by linarith)
  have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hM2 : (M : ℝ) + 2 ≠ 0 := by positivity
  field_simp

/-- Source: note Section 2.2, `σ̄ = sqrt(v μ)`. -/
noncomputable def sigma (q mu : ℝ) : ℝ := Real.sqrt (variance q * mu)

/-- Source: note Section 2.2, `a_G = exp(-1/2)/sqrt(2π)`. -/
noncomputable def gaussianA : ℝ := Real.exp (-(1 / 2 : ℝ)) / Real.sqrt (2 * Real.pi)

/-- Source: note Section 2.2, the fiber function, with its original normalization. -/
noncomputable def fiber (q mu : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  sigma q mu ^ 3 * weightedKernel q M j / (4 * variance q ^ 2 * gaussianA) +
    offset q M j ^ 2 / sigma q mu ^ 2

/-- Source: note Lemma 3.1, the fiber normalization (equation (3.1)). -/
theorem fiber_eq {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (M : ℕ) (j : ℤ) :
    fiber q mu M j =
      mu ^ (3 / 2 : ℝ) * Real.sqrt (1 - signedR q ^ 2) * binom (M + 2) q (j + 1) /
        (2 * gaussianA * ((M : ℝ) + 1)) * (bonus q M - squareOffset q M j) +
      (((M : ℝ) + 2) / mu) * squareOffset q M j := by
  have hv : 0 < variance q := mul_pos hq0 (by linarith)
  have hs : sigma q mu ^ 2 = variance q * mu := Real.sq_sqrt (by positivity)
  have hpow : mu ^ (3 / 2 : ℝ) = Real.sqrt mu ^ 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hmu.le]
    norm_num
  have hroot : Real.sqrt (1 - signedR q ^ 2) = 2 * Real.sqrt (variance q) := by
    rw [one_sub_signedR_sq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  have hsig : sigma q mu = Real.sqrt (variance q) * Real.sqrt mu :=
    Real.sqrt_mul hv.le mu
  have hva : Real.sqrt (variance q) ^ 2 = variance q := Real.sq_sqrt hv.le
  have hga : gaussianA ≠ 0 := by
    unfold gaussianA
    exact div_ne_zero (Real.exp_ne_zero _) (ne_of_gt (Real.sqrt_pos.2 (by positivity)))
  have hm1 : (M : ℝ) + 1 ≠ 0 := by positivity
  have hm2 : (M : ℝ) + 2 ≠ 0 := by positivity
  unfold fiber
  rw [weightedKernel_eq_normalized hq0 hq1, hs, hpow, hroot, hsig]
  unfold squareOffset
  field_simp
  rw [← hva]
  simp only [Real.sqrt_sq (Real.sqrt_nonneg (variance q))]
  ring

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.weightL
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightL
#check Erdos993Lean.Analytic.V22.Analysis.weightR
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightR
#check Erdos993Lean.Analytic.V22.Analysis.signedR
#print axioms Erdos993Lean.Analytic.V22.Analysis.signedR
#check Erdos993Lean.Analytic.V22.Analysis.variance
#print axioms Erdos993Lean.Analytic.V22.Analysis.variance
#check Erdos993Lean.Analytic.V22.Analysis.offset
#print axioms Erdos993Lean.Analytic.V22.Analysis.offset
#check Erdos993Lean.Analytic.V22.Analysis.squareOffset
#print axioms Erdos993Lean.Analytic.V22.Analysis.squareOffset
#check Erdos993Lean.Analytic.V22.Analysis.bonus
#print axioms Erdos993Lean.Analytic.V22.Analysis.bonus
#check Erdos993Lean.Analytic.V22.Analysis.weightedKernel
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightedKernel
#check Erdos993Lean.Analytic.V22.Analysis.weights_nonneg
#print axioms Erdos993Lean.Analytic.V22.Analysis.weights_nonneg
#check Erdos993Lean.Analytic.V22.Analysis.one_sub_signedR_sq
#print axioms Erdos993Lean.Analytic.V22.Analysis.one_sub_signedR_sq
#check Erdos993Lean.Analytic.V22.Analysis.offset_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.offset_eq
#check Erdos993Lean.Analytic.V22.Analysis.weightedKernel_mul
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightedKernel_mul
#check Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq
#check Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq_normalized
#print axioms Erdos993Lean.Analytic.V22.Analysis.weightedKernel_eq_normalized
#check Erdos993Lean.Analytic.V22.Analysis.sigma
#print axioms Erdos993Lean.Analytic.V22.Analysis.sigma
#check Erdos993Lean.Analytic.V22.Analysis.gaussianA
#print axioms Erdos993Lean.Analytic.V22.Analysis.gaussianA
#check Erdos993Lean.Analytic.V22.Analysis.fiber
#print axioms Erdos993Lean.Analytic.V22.Analysis.fiber
#check Erdos993Lean.Analytic.V22.Analysis.fiber_eq
#print axioms Erdos993Lean.Analytic.V22.Analysis.fiber_eq
