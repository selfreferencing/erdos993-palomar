module

public import Erdos993Lean.Analytic.V213.LowMeanMass

/-!
Algebraic kernel identities for the full integer axis, including
the two outside-support ranks in equation `r12:eq55` and its following
sentence. Source: version 2.13 of the manuscript.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_binom_above {M : ℕ} {q : ℝ} {j : ℤ} (hj : (M : ℤ) < j) :
    binom M q j = 0 := by
  simp [binom, not_le.mpr hj]

theorem lowMean_fL_factor {M n : ℕ} (hn : n ≤ M) (q : ℝ) :
    fL q M (n : ℤ) = (1 - q) * binom M q (n : ℤ) *
      (((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n)) := by
  have hnR : (n : ℝ) ≤ M := by exact_mod_cast hn
  have hden : (M : ℝ) + 1 - n ≠ 0 := by linarith
  cases n with
  | zero =>
    unfold fL
    simp only [Nat.cast_zero, sub_zero] at hden ⊢
    rw [binom_negative M q (by norm_num : (0 : ℤ) - 1 < 0)]
    simp [hden]
  | succ n =>
    have he : ((n + 1 : ℕ) : ℤ) - 1 = (n : ℤ) := by omega
    have hb := lowMean_binom_adjacent (by omega : n < M) q
    unfold fL
    rw [he]
    push_cast at hb hden hnR ⊢
    rw [mul_div_assoc']
    apply (eq_div_iff hden).mpr
    linear_combination hb

theorem lowMean_fR_factor {M n : ℕ} (hn : n ≤ M) (q : ℝ) :
    fR q M (n : ℤ) = q * binom M q (n : ℤ) *
      ((2 * (n : ℝ) + 1 - M) / ((n : ℝ) + 1)) := by
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  by_cases hlt : n < M
  · have hb := lowMean_binom_adjacent hlt q
    unfold fR
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
    rw [mul_div_assoc']
    apply (eq_div_iff hden).mpr
    linear_combination -hb
  · have he : n = M := by omega
    subst n
    unfold fR
    rw [lowMean_binom_above (by omega : (M : ℤ) < (M : ℤ) + 1)]
    field_simp
    ring

theorem lowMean_binom_reflect_nat {M n : ℕ} (hn : n ≤ M) (q : ℝ) :
    binom M (1 - q) ((M - n : ℕ) : ℤ) = binom M q (n : ℤ) := by
  rw [binom_nat, binom_nat, Nat.choose_symm hn, Nat.sub_sub_self hn]
  have he : 1 - (1 - q) = q := by ring
  rw [he]
  ring

theorem lowMean_binom_reflect (M : ℕ) (q : ℝ) (j : ℤ) :
    binom M (1 - q) ((M : ℤ) - j) = binom M q j := by
  by_cases hj0 : j < 0
  · rw [binom_negative M q hj0, lowMean_binom_above (by omega)]
  · by_cases hjM : (M : ℤ) < j
    · rw [lowMean_binom_above hjM, binom_negative M (1 - q) (by omega)]
    · lift j to ℕ using (by omega : 0 ≤ j)
      have hn : j ≤ M := by omega
      have he : ((M - j : ℕ) : ℤ) = (M : ℤ) - j := by omega
      rw [← he]
      exact lowMean_binom_reflect_nat hn q

/-- Reflection interchanges the left and right kernel weights. -/
theorem lowMean_kernel_reflect (M : ℕ) (q wL wR : ℝ) (j : ℤ) :
    kernel2 (1 - q) wR wL M ((M : ℤ) - j) = kernel2 q wL wR M j := by
  unfold kernel2 fL fR
  rw [show (M : ℤ) - j - 1 = (M : ℤ) - (j + 1) by omega,
    show (M : ℤ) - j + 1 = (M : ℤ) - (j - 1) by omega]
  simp only [lowMean_binom_reflect]
  have he : 1 - (1 - q) = q := by ring
  rw [he]
  ring

theorem lowMean_kernel_neg_one (M : ℕ) {q : ℝ} (hq1 : q < 1) (wL wR : ℝ) :
    kernel2 q wL wR M (-1) = -wR * (1 - q) ^ M := by
  have h1 : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hb0 : binom M q 0 = (1 - q) ^ M := by
    rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, binom_nat]
    simp
  unfold kernel2 fL fR
  rw [binom_negative M q (by norm_num : (-1 : ℤ) < 0),
    binom_negative M q (by norm_num : (-1 : ℤ) - 1 < 0)]
  norm_num only [neg_add_cancel] at *
  rw [hb0]
  field_simp
  ring

theorem lowMean_kernel_top (M : ℕ) {q : ℝ} (hq0 : 0 < q) (wL wR : ℝ) :
    kernel2 q wL wR M ((M : ℤ) + 1) = -wL * q ^ M := by
  have hr := lowMean_kernel_neg_one M (q := 1 - q) (by linarith) wR wL
  rw [← lowMean_kernel_reflect M q wL wR ((M : ℤ) + 1)]
  simpa using hr

theorem lowMean_kernel_outside (M : ℕ) (q wL wR : ℝ) (j : ℤ)
    (hj : j < -1 ∨ (M : ℤ) + 1 < j) : kernel2 q wL wR M j = 0 := by
  unfold kernel2 fL fR
  rcases hj with hj | hj
  · rw [binom_negative M q (by omega : j < 0),
      binom_negative M q (by omega : j - 1 < 0), binom_negative M q (by omega : j + 1 < 0)]
    ring
  · rw [lowMean_binom_above (by omega : (M : ℤ) < j),
      lowMean_binom_above (by omega : (M : ℤ) < j - 1),
      lowMean_binom_above (by omega : (M : ℤ) < j + 1)]
    ring

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fL_factor
#print axioms Erdos993Lean.Analytic.V213.lowMean_fR_factor
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_reflect
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_neg_one
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_top
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_outside
