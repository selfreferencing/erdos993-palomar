module

public import Erdos993Lean.Analytic.V213.LowMeanKernelLower

/-!
The first kernel bound following Lemma 6.5, on the whole integer
axis. The disjoint negative ranges and reflection are proved from fL/fR.
No generated finite family is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_fL_nonneg (M : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {j : ℤ} (hj : 2 * j ≤ (M : ℤ) + 1) : 0 ≤ fL q M j / q := by
  by_cases hj0 : j < 0
  · simp [fL, binom_negative M q hj0, binom_negative M q (by omega : j - 1 < 0)]
  · lift j to ℕ using (by omega : 0 ≤ j)
    have hn : j ≤ M := by omega
    have hnR : (j : ℝ) ≤ M := by exact_mod_cast hn
    have hjR : 2 * (j : ℝ) ≤ (M : ℝ) + 1 := by exact_mod_cast hj
    rw [lowMean_fL_factor hn]
    exact div_nonneg (mul_nonneg
      (mul_nonneg (sub_pos.mpr hq1).le (lowMean_binom_nonneg M j hq0.le hq1.le))
      (div_nonneg (by linarith) (by linarith))) hq0.le

theorem lowMean_fR_reflect (M : ℕ) (q : ℝ) (j : ℤ) :
    fR q M j = fL (1 - q) M ((M : ℤ) - j) := by
  unfold fL fR
  rw [show (M : ℤ) - j - 1 = (M : ℤ) - (j + 1) by omega]
  simp only [lowMean_binom_reflect]
  ring

theorem lowMean_fR_nonneg (M : ℕ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    {j : ℤ} (hj : (M : ℤ) - 1 ≤ 2 * j) : 0 ≤ fR q M j / (1 - q) := by
  rw [lowMean_fR_reflect]
  exact lowMean_fL_nonneg M (by linarith) (by linarith) (by omega)

theorem lowMean_fR_negativeG {M n : ℕ} (hn : n < M) {q : ℝ}
    (hq1 : q < 1) : fR q M (n : ℤ) / (1 - q) = -lowMeanG M (n + 1) q := by
  have hnR : (n : ℝ) < M := by exact_mod_cast hn
  have hden : (M : ℝ) - n ≠ 0 := by linarith
  have hq : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  have hb := lowMean_binom_adjacent hn q
  push_cast at hb
  unfold fR lowMeanG
  rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega]
  push_cast
  rw [show (M : ℝ) + 1 - ((n : ℝ) + 1) = (M : ℝ) - n by ring]
  apply (div_eq_iff hq).mpr
  apply mul_left_cancel₀ hden
  field_simp
  linear_combination -hb

/-- In the lower negative range only the right kernel term can be negative. -/
theorem lowMean_kernel_lower_range {M : ℕ} {j : ℤ} {l h q wL wR : ℝ}
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hl : 0 < l) (hh : h < 1)
    (hq : q ∈ Set.Icc l h) (hj0 : -1 ≤ j) (hjM : 2 * j < (M : ℤ) - 1) :
    -wR * lowMeanClosedMaximum M l ≤ kernel2 q wL wR M j := by
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  by_cases hj : j = -1
  · rw [hj, lowMean_kernel_neg_one M hq1]
    have hb := lowMean_closedMaximum M hl hh hq 0 (by omega)
    rw [lowMeanG_zero] at hb
    exact mul_le_mul_of_nonpos_left hb (by linarith)
  · have hjNat : 0 ≤ j := by omega
    lift j to ℕ using hjNat
    have hn : j < M := by omega
    have hng : j + 1 ≤ M / 2 := by omega
    have hleft := mul_nonneg hwL (lowMean_fL_nonneg M hq0 hq1 (by omega : 2 * (j : ℤ) ≤ (M : ℤ) + 1))
    have hright := mul_le_mul_of_nonpos_left (lowMean_closedMaximum M hl hh hq (j + 1) hng)
      (show -wR ≤ 0 by linarith)
    unfold kernel2
    rw [mul_div_assoc, mul_div_assoc, lowMean_fR_negativeG hn hq1]
    linarith

noncomputable def lowMeanKernelK (M : ℕ) (j : ℤ) (wL wR l h : ℝ) : ℝ :=
  if -1 ≤ j ∧ 2 * j < (M : ℤ) - 1 then wR * lowMeanClosedMaximum M l
  else if j ≤ (M : ℤ) + 1 ∧ (M : ℤ) + 1 < 2 * j then
    wL * lowMeanClosedMaximum M (1 - h)
  else 0

/-- The printed disjoint-range lower bound, including both infinite tails. -/
theorem lowMean_kernel_first_lower (M : ℕ) (j : ℤ) {l h q wL wR : ℝ}
    (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hl : 0 < l) (hh : h < 1)
    (hq : q ∈ Set.Icc l h) : -lowMeanKernelK M j wL wR l h ≤ kernel2 q wL wR M j := by
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  unfold lowMeanKernelK
  split_ifs with hlow hhigh
  · simpa only [neg_mul] using lowMean_kernel_lower_range hwL hwR hl hh hq hlow.1 hlow.2
  · rw [← lowMean_kernel_reflect M q wL wR j]
    have hr := lowMean_kernel_lower_range (M := M) hwR hwL (l := 1 - h) (h := 1 - l)
      (q := 1 - q) (by linarith) (by linarith)
      ⟨by linarith [hq.2], by linarith [hq.1]⟩
      (j := (M : ℤ) - j) (by omega) (by omega)
    simpa only [neg_mul] using hr
  · by_cases hout : j < -1 ∨ (M : ℤ) + 1 < j
    · rw [lowMean_kernel_outside M q wL wR j hout]
      simp
    · have hjL : 2 * j ≤ (M : ℤ) + 1 := by omega
      have hjR : (M : ℤ) - 1 ≤ 2 * j := by omega
      have hleft := mul_nonneg hwL (lowMean_fL_nonneg M hq0 hq1 hjL)
      have hright := mul_nonneg hwR (lowMean_fR_nonneg M hq0 hq1 hjR)
      unfold kernel2
      simp only [neg_zero, mul_div_assoc]
      exact add_nonneg hleft hright

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fL_nonneg
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_first_lower
