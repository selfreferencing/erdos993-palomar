module

public import Erdos993Lean.Analytic.MGF.Criterion

/-!
The binomial heat recurrence and priced-seed tail propagation.
Source: version 2.13 of the manuscript, Lemma 6.1 (`r12:lem9`), equations `r12:eq46`–`r12:eq47`.
All integer ranks, including ranks outside
the binomial support, are included.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem binom_nat (M n : ℕ) (q : ℝ) :
    binom M q (n : ℤ) = (M.choose n : ℝ) * q ^ n * (1 - q) ^ (M - n) := by
  by_cases hn : n ≤ M
  · simp [binom, hn]
  · have hz := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hn)
    simp [binom, hn, hz]

theorem binom_negative (M : ℕ) (q : ℝ) {j : ℤ} (hj : j < 0) :
    binom M q j = 0 := by
  simp [binom, not_le.mpr hj]

theorem binom_succ_nat (M n : ℕ) (q : ℝ) :
    binom (M + 1) q ((n + 1 : ℕ) : ℤ) =
      q * binom M q (n : ℤ) + (1 - q) * binom M q ((n + 1 : ℕ) : ℤ) := by
  simp only [binom_nat]
  rcases lt_trichotomy n M with hn | rfl | hn
  · rw [Nat.choose_succ_succ', Nat.cast_add]
    have he : M - n = M - (n + 1) + 1 := by omega
    have he' : M + 1 - (n + 1) = M - n := by omega
    rw [he', he, pow_succ, pow_succ]
    ring
  · simp [Nat.choose_succ_self, pow_succ]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega : M + 1 < n + 1),
      Nat.choose_eq_zero_of_lt hn,
      Nat.choose_eq_zero_of_lt (by omega : M < n + 1)]
    simp

/-- Pascal's averaging identity, with the binomial mass extended by zero. -/
theorem binom_heat (M : ℕ) (q : ℝ) (j : ℤ) :
    binom (M + 1) q j = q * binom M q (j - 1) + (1 - q) * binom M q j := by
  rcases lt_trichotomy j 0 with hj | rfl | hj
  · rw [binom_negative _ _ hj, binom_negative _ _ (by omega), binom_negative _ _ hj]
    ring
  · have hm : binom M q (0 - 1) = 0 := binom_negative M q (by norm_num)
    rw [hm]
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, binom_nat, binom_nat]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.sub_zero,
      mul_zero, zero_add, pow_succ]
    ring
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j - 1)
    have hjn : j = ((n + 1 : ℕ) : ℤ) := by omega
    simpa [hjn] using binom_succ_nat M n q

/-- The two-sided kernel commutes with binomial averaging. -/
theorem kernel2_heat (q wL wR : ℝ) (M : ℕ) (j : ℤ) :
    kernel2 q wL wR (M + 1) j =
      q * kernel2 q wL wR M (j - 1) + (1 - q) * kernel2 q wL wR M j := by
  unfold kernel2 fL fR
  simp only [binom_heat]
  have hj : j - 1 + 1 = j := by omega
  have hj' : j + 1 - 1 = j := by omega
  rw [hj, hj']
  ring

/-- The penalized kernel h_M(j) printed just before Lemma 6.1. -/
noncomputable def lowMeanH (q wL wR xi eta : ℝ) (M : ℕ) (j : ℤ) : ℝ :=
  kernel2 q wL wR M j + xi * ((j : ℝ) - q * M) +
    eta * ((j : ℝ) - q * M) ^ 2

/-- The paper's concave quadratic, also evaluated at nonintegral means. -/
def lowMeanPsi (alpha beta gamma m0 m : ℝ) : ℝ :=
  alpha + beta * (m - m0) - gamma * (m - m0) ^ 2

/-- Lemma 6.1, heat recurrence, equation `r12:eq47`. -/
theorem lowMeanH_heat (q wL wR xi eta : ℝ) (M : ℕ) (j : ℤ) :
    lowMeanH q wL wR xi eta (M + 1) j =
      q * lowMeanH q wL wR xi eta M (j - 1) +
        (1 - q) * lowMeanH q wL wR xi eta M j - eta * q * (1 - q) := by
  unfold lowMeanH
  rw [kernel2_heat]
  push_cast
  ring

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.binom_heat
#print axioms Erdos993Lean.Analytic.V213.kernel2_heat
#print axioms Erdos993Lean.Analytic.V213.lowMeanH_heat
