module

public import Mathlib
public import Erdos993Lean.Analytic.Defs

/-!
# Binomial point masses: basic facts and the step relations

Source: T1, §1, proof of Lemma 1.1 (the ratio
relations between `b_M`, `b_{M+1}` and `b_{M+2}`).  The point mass is `binom M q j = b_M(j; q)` of
`Erdos993Lean/Analytic/Defs.lean`, extended by zero outside `0 ≤ j ≤ M`.

## Results (namespace `Erdos993Lean.Analytic.NoValley`)

* `binom_of_neg`, `binom_of_gt`, `binom_natCast`, `binom_natCast_of_le`: evaluation.
* `binom_nonneg`, `sum_binom` (`∑_{j ≤ M} b_M(j) = 1`), `binom_le_one` (for `0 ≤ q ≤ 1`).
* The one-step relations, valid for **every** integer `j` (the boundary cases included):
  `binom_step_right`: `(M + 1)(1 − q) b_M(j) = (M + 1 − j) b_{M+1}(j)`;
  `binom_step_left`:  `(M + 1) q b_M(j − 1) = j b_{M+1}(j)`.
* The two-step relations (`N = M + 2`, `i = j + 1`, `v = q(1 − q)`), for every integer `j`:
  `binom_two_step_mid`:   `N(N − 1) v b_M(j) = i (N − i) b_N(i)`;
  `binom_two_step_left`:  `N(N − 1) q² b_M(j − 1) = i (i − 1) b_N(i)`;
  `binom_two_step_right`: `N(N − 1) (1 − q)² b_M(j + 1) = (N − i)(N − i − 1) b_N(i)`.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.NoValley

open Finset

/-! ## Evaluation -/

theorem binom_of_neg {M : ℕ} {q : ℝ} {j : ℤ} (hj : j < 0) : binom M q j = 0 := by
  unfold binom
  rw [if_neg (by omega)]

theorem binom_of_gt {M : ℕ} {q : ℝ} {j : ℤ} (hj : (M : ℤ) < j) : binom M q j = 0 := by
  unfold binom
  rw [if_neg (by omega)]

theorem binom_natCast (M n : ℕ) (q : ℝ) :
    binom M q (n : ℤ) =
      if n ≤ M then ((M.choose n : ℕ) : ℝ) * q ^ n * (1 - q) ^ (M - n) else 0 := by
  unfold binom
  by_cases h : n ≤ M
  · rw [if_pos (by omega), if_pos h, Int.toNat_natCast]
  · rw [if_neg (by omega), if_neg h]

theorem binom_natCast_of_le {M n : ℕ} (q : ℝ) (h : n ≤ M) :
    binom M q (n : ℤ) = ((M.choose n : ℕ) : ℝ) * q ^ n * (1 - q) ^ (M - n) := by
  rw [binom_natCast, if_pos h]

theorem binom_natCast_of_lt {M n : ℕ} (q : ℝ) (h : M < n) : binom M q (n : ℤ) = 0 := by
  rw [binom_natCast, if_neg (by omega)]

/-! ## Positivity and total mass -/

theorem binom_nonneg {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) : 0 ≤ binom M q j := by
  unfold binom
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))
      (pow_nonneg (by linarith) _)
  · exact le_refl 0

/-- The binomial masses sum to one. -/
theorem sum_binom (M : ℕ) (q : ℝ) : ∑ n ∈ range (M + 1), binom M q (n : ℤ) = 1 := by
  have h := add_pow q (1 - q) M
  have e : q + (1 - q) = 1 := by ring
  rw [e, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [binom_natCast_of_le q (Nat.lt_succ_iff.mp (mem_range.mp hn))]
  ring

theorem binom_le_one {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (j : ℤ) : binom M q j ≤ 1 := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [binom_of_neg hj]
    norm_num
  · lift j to ℕ using hj
    by_cases hjM : j ≤ M
    · rw [← sum_binom M q]
      exact Finset.single_le_sum (f := fun n : ℕ => binom M q (n : ℤ))
        (fun n _ => binom_nonneg hq0 hq1 _) (mem_range.mpr (Nat.lt_succ_of_le hjM))
    · rw [binom_natCast_of_lt q (by omega)]
      norm_num

/-! ## The one-step relations -/

/-- `(M + 1)(1 − q) b_M(j) = (M + 1 − j) b_{M+1}(j)` for every integer `j`. -/
theorem binom_step_right (M : ℕ) (q : ℝ) (j : ℤ) :
    ((M : ℝ) + 1) * (1 - q) * binom M q j = ((M : ℝ) + 1 - j) * binom (M + 1) q j := by
  rcases lt_or_ge j 0 with hj | hj
  · rw [binom_of_neg hj, binom_of_neg hj]
    ring
  lift j to ℕ using hj
  rcases lt_trichotomy j (M + 1) with hlt | heq | hgt
  · have hle : j ≤ M := by omega
    rw [binom_natCast_of_le q hle, binom_natCast_of_le q hlt.le]
    have hc := Nat.choose_mul_succ_eq M j
    have hc' : ((M.choose j : ℕ) : ℝ) * ((M : ℝ) + 1) =
        (((M + 1).choose j : ℕ) : ℝ) * ((M : ℝ) + 1 - j) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hc
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub (by omega)]
      push_cast
      ring
    have hp : M + 1 - j = (M - j) + 1 := by omega
    rw [hp, pow_succ]
    push_cast
    linear_combination (q ^ j * (1 - q) ^ (M - j) * (1 - q)) * hc'
  · subst heq
    rw [binom_natCast_of_lt q (by omega)]
    push_cast
    ring
  · rw [binom_natCast_of_lt q (by omega), binom_natCast_of_lt q (by omega)]
    ring

/-- `(M + 1) q b_M(j − 1) = j b_{M+1}(j)` for every integer `j`. -/
theorem binom_step_left (M : ℕ) (q : ℝ) (j : ℤ) :
    ((M : ℝ) + 1) * q * binom M q (j - 1) = (j : ℝ) * binom (M + 1) q j := by
  rcases lt_or_ge j 1 with hj | hj
  · rw [binom_of_neg (by omega : j - 1 < 0)]
    rcases lt_or_ge j 0 with hj' | hj'
    · rw [binom_of_neg hj']
      ring
    · have : j = 0 := by omega
      subst this
      simp
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = (n : ℤ) + 1 := ⟨(j - 1).toNat, by omega⟩
  have e1 : (n : ℤ) + 1 - 1 = (n : ℤ) := by ring
  have e2 : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [e1, e2]
  by_cases hn : n ≤ M
  · rw [binom_natCast_of_le q hn, binom_natCast_of_le q (by omega : n + 1 ≤ M + 1)]
    have hc := Nat.add_one_mul_choose_eq M n
    have hc' : ((M : ℝ) + 1) * ((M.choose n : ℕ) : ℝ) =
        (((M + 1).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1) := by
      have := congrArg (fun x : ℕ => (x : ℝ)) hc
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at this
      exact this
    have hp : M + 1 - (n + 1) = M - n := by omega
    rw [hp, pow_succ]
    push_cast
    linear_combination (q ^ n * (1 - q) ^ (M - n) * q) * hc'
  · rw [binom_natCast_of_lt q (by omega), binom_natCast_of_lt q (by omega : M + 1 < n + 1)]
    ring

/-! ## The two-step relations (`N = M + 2`, `i = j + 1`) -/

/-- `N(N − 1) q(1 − q) b_M(j) = i (N − i) b_N(i)` with `N = M + 2`, `i = j + 1`. -/
theorem binom_two_step_mid (M : ℕ) (q : ℝ) (j : ℤ) :
    ((M : ℝ) + 2) * ((M : ℝ) + 1) * (q * (1 - q)) * binom M q j =
      ((j : ℝ) + 1) * ((M : ℝ) + 1 - j) * binom (M + 2) q (j + 1) := by
  have h1 := binom_step_right M q j
  have h2 := binom_step_left (M + 1) q (j + 1)
  rw [add_sub_cancel_right] at h2
  push_cast at h1 h2
  linear_combination ((M : ℝ) + 2) * q * h1 + ((M : ℝ) + 1 - j) * h2

/-- `N(N − 1) q² b_M(j − 1) = i (i − 1) b_N(i)` with `N = M + 2`, `i = j + 1`. -/
theorem binom_two_step_left (M : ℕ) (q : ℝ) (j : ℤ) :
    ((M : ℝ) + 2) * ((M : ℝ) + 1) * q ^ 2 * binom M q (j - 1) =
      ((j : ℝ) + 1) * (j : ℝ) * binom (M + 2) q (j + 1) := by
  have h1 := binom_step_left M q j
  have h2 := binom_step_left (M + 1) q (j + 1)
  rw [add_sub_cancel_right] at h2
  push_cast at h1 h2
  linear_combination ((M : ℝ) + 2) * q * h1 + (j : ℝ) * h2

/-- `N(N − 1)(1 − q)² b_M(j + 1) = (N − i)(N − i − 1) b_N(i)` with `N = M + 2`, `i = j + 1`. -/
theorem binom_two_step_right (M : ℕ) (q : ℝ) (j : ℤ) :
    ((M : ℝ) + 2) * ((M : ℝ) + 1) * (1 - q) ^ 2 * binom M q (j + 1) =
      ((M : ℝ) + 1 - j) * ((M : ℝ) - j) * binom (M + 2) q (j + 1) := by
  have h1 := binom_step_right M q (j + 1)
  have h2 := binom_step_right (M + 1) q (j + 1)
  push_cast at h1 h2
  linear_combination ((M : ℝ) + 2) * (1 - q) * h1 + ((M : ℝ) - j) * h2

end Erdos993Lean.Analytic.NoValley

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.NoValley.binom_of_neg
#print axioms Erdos993Lean.Analytic.NoValley.binom_of_neg
#check Erdos993Lean.Analytic.NoValley.binom_of_gt
#print axioms Erdos993Lean.Analytic.NoValley.binom_of_gt
#check Erdos993Lean.Analytic.NoValley.binom_natCast
#print axioms Erdos993Lean.Analytic.NoValley.binom_natCast
#check Erdos993Lean.Analytic.NoValley.binom_natCast_of_le
#print axioms Erdos993Lean.Analytic.NoValley.binom_natCast_of_le
#check Erdos993Lean.Analytic.NoValley.binom_natCast_of_lt
#print axioms Erdos993Lean.Analytic.NoValley.binom_natCast_of_lt
#check Erdos993Lean.Analytic.NoValley.binom_nonneg
#print axioms Erdos993Lean.Analytic.NoValley.binom_nonneg
#check Erdos993Lean.Analytic.NoValley.sum_binom
#print axioms Erdos993Lean.Analytic.NoValley.sum_binom
#check Erdos993Lean.Analytic.NoValley.binom_le_one
#print axioms Erdos993Lean.Analytic.NoValley.binom_le_one
#check Erdos993Lean.Analytic.NoValley.binom_step_right
#print axioms Erdos993Lean.Analytic.NoValley.binom_step_right
#check Erdos993Lean.Analytic.NoValley.binom_step_left
#print axioms Erdos993Lean.Analytic.NoValley.binom_step_left
#check Erdos993Lean.Analytic.NoValley.binom_two_step_mid
#print axioms Erdos993Lean.Analytic.NoValley.binom_two_step_mid
#check Erdos993Lean.Analytic.NoValley.binom_two_step_left
#print axioms Erdos993Lean.Analytic.NoValley.binom_two_step_left
#check Erdos993Lean.Analytic.NoValley.binom_two_step_right
#print axioms Erdos993Lean.Analytic.NoValley.binom_two_step_right
