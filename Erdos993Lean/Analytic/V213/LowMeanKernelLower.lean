module

public import Erdos993Lean.Analytic.V213.LowMeanKernelMonomials
public import Erdos993Lean.Analytic.V213.LowMeanClosedMaximum

/-!
The second whole-interval kernel bound r12:eq53. Its mass bounds
and the three possible coefficient-sign cases are proved analytically.
No generated certificate family is consumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_binom_monotone {M n : ℕ} (hn : n ≤ M) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hmode : M * b ≤ (n : ℝ)) :
    MonotoneOn (fun q : ℝ => binom M q (n : ℤ)) (Set.Icc a b) := by
  have hd q (hq : q ∈ Set.Icc a b) := lowMean_binom_hasDerivAt hn
    (lt_of_lt_of_le ha hq.1) (lt_of_le_of_lt hq.2 hb)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
    (fun q hq => (hd q hq).continuousAt.continuousWithinAt)
    (fun q hq => (hd q (interior_subset hq)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc a b := interior_subset hq
  have hq0 := lt_of_lt_of_le ha hq'.1
  have hq1 := lt_of_le_of_lt hq'.2 hb
  have hMq := mul_le_mul_of_nonneg_left hq'.2 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  exact div_nonneg
    (mul_nonneg (lowMean_binom_nonneg M n hq0.le hq1.le) (by linarith))
    (mul_nonneg hq0.le (sub_nonneg.mpr hq1.le))

/-- The mass minimum on a closed interval is at an endpoint, including M=0. -/
theorem lowMean_binom_endpoint_min {M n : ℕ} (hn : n ≤ M) {l h q : ℝ}
    (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h) :
    min (binom M l (n : ℤ)) (binom M h (n : ℤ)) ≤ binom M q (n : ℤ) := by
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  rcases le_total (M * q) (n : ℝ) with hm | hm
  · exact le_trans (min_le_left _ _) (lowMean_binom_monotone hn hl hq1 hm
      ⟨le_rfl, hq.1⟩ ⟨hq.1, le_rfl⟩ hq.1)
  · exact le_trans (min_le_right _ _) (lowMean_binom_antitone hn hq0 hh hm
      ⟨le_rfl, hq.2⟩ ⟨hq.2, le_rfl⟩ hq.2)

noncomputable def lowMeanMassMode (M n : ℕ) (l h : ℝ) : ℝ :=
  if M = 0 then l else max l (min h ((n : ℝ) / M))

/-- The mass maximum is at the clipped mode; M=0 uses mass 1. -/
theorem lowMean_binom_clipped_max {M n : ℕ} (hn : n ≤ M) {l h q : ℝ}
    (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h) :
    binom M q (n : ℤ) ≤ binom M (lowMeanMassMode M n l h) (n : ℤ) := by
  have hlh := le_trans hq.1 hq.2
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  unfold lowMeanMassMode
  by_cases hM : M = 0
  · subst M
    have hn0 : n = 0 := by omega
    subst n
    simp [binom]
  · rw [ite_eq_right hM]
    have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
    let m : ℝ := (n : ℝ) / M
    have hMm : (M : ℝ) * m = n := by dsimp [m]; field_simp
    by_cases hml : m ≤ l
    · rw [min_eq_right (le_trans hml hlh), max_eq_left hml]
      exact lowMean_binom_antitone hn hl hq1 (by nlinarith)
        ⟨le_rfl, hq.1⟩ ⟨hq.1, le_rfl⟩ hq.1
    · by_cases hhm : h ≤ m
      · rw [min_eq_left hhm, max_eq_right hlh]
        exact lowMean_binom_monotone hn hq0 hh (by nlinarith)
          ⟨le_rfl, hq.2⟩ ⟨hq.2, le_rfl⟩ hq.2
      · have hlm : l ≤ m := le_of_not_ge hml
        have hmh : m ≤ h := le_of_not_ge hhm
        rw [min_eq_right hmh, max_eq_right hlm]
        have hm0 := lt_of_lt_of_le hl hlm
        have hm1 := lt_of_le_of_lt hmh hh
        rcases le_total q m with hqm | hmq
        · exact lowMean_binom_monotone hn hq0 hm1 hMm.le
            ⟨le_rfl, hqm⟩ ⟨hqm, le_rfl⟩ hqm
        · exact lowMean_binom_antitone hn hm0 hq1 hMm.ge
            ⟨le_rfl, hmq⟩ ⟨hmq, le_rfl⟩ hmq

noncomputable def lowMeanMultiplier (a b q : ℝ) : ℝ := a * (1 - q) / q + b * q / (1 - q)
noncomputable def lowMeanMultiplierLower (a b l h : ℝ) : ℝ :=
  if 0 ≤ a ∧ b ≤ 0 then lowMeanMultiplier a b h
  else if a ≤ 0 ∧ 0 ≤ b then lowMeanMultiplier a b l
  else a * (1 - h) / h + b * l / (1 - l)

theorem lowMean_odds_bounds {l h q : ℝ} (hl : 0 < l) (hh : h < 1)
    (hq : q ∈ Set.Icc l h) :
    (1 - h) / h ≤ (1 - q) / q ∧ (1 - q) / q ≤ (1 - l) / l ∧
      l / (1 - l) ≤ q / (1 - q) ∧ q / (1 - q) ≤ h / (1 - h) := by
  have hq0 := lt_of_lt_of_le hl hq.1
  have hh0 := lt_of_lt_of_le hq0 hq.2
  have hl1 := lt_of_le_of_lt hq.1 (lt_of_le_of_lt hq.2 hh)
  have hq1 := lt_of_le_of_lt hq.2 hh
  constructor
  · apply (div_le_div_iff₀ hh0 hq0).mpr
    nlinarith [hq.2]
  constructor
  · apply (div_le_div_iff₀ hq0 hl).mpr
    nlinarith [hq.1]
  constructor
  · apply (div_le_div_iff₀ (sub_pos.mpr hl1) (sub_pos.mpr hq1)).mpr
    nlinarith [hq.1]
  · apply (div_le_div_iff₀ (sub_pos.mpr hq1) (sub_pos.mpr hh)).mpr
    nlinarith [hq.2]

/-- The printed cases exhaust the possibilities when the two coefficients
cannot both be negative, as is the case for the kernel coefficients. -/
theorem lowMean_multiplier_lower {a b l h q : ℝ}
    (hab : 0 ≤ a ∨ 0 ≤ b) (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h) :
    lowMeanMultiplierLower a b l h ≤ lowMeanMultiplier a b q := by
  obtain ⟨h1, h2, h3, h4⟩ := lowMean_odds_bounds hl hh hq
  unfold lowMeanMultiplierLower lowMeanMultiplier
  split_ifs with hs ht
  · have ha := mul_le_mul_of_nonneg_left h1 hs.1
    have hb := mul_le_mul_of_nonpos_left h4 hs.2
    simpa only [mul_div_assoc] using add_le_add ha hb
  · have ha := mul_le_mul_of_nonpos_left h2 ht.1
    have hb := mul_le_mul_of_nonneg_left h3 ht.2
    simpa only [mul_div_assoc] using add_le_add ha hb
  · have ha0 : 0 ≤ a := by rcases hab with ha | hb; exact ha; by_contra ha; exact ht ⟨le_of_not_ge ha, hb⟩
    have hb0 : 0 ≤ b := by by_contra hb; exact hs ⟨ha0, le_of_not_ge hb⟩
    simpa only [mul_div_assoc] using add_le_add
      (mul_le_mul_of_nonneg_left h1 ha0) (mul_le_mul_of_nonneg_left h3 hb0)

noncomputable def lowMeanKernelL (M n : ℕ) (a b l h : ℝ) : ℝ :=
  let k := lowMeanMultiplierLower a b l h
  if 0 ≤ k then k * min (binom M l (n : ℤ)) (binom M h (n : ℤ))
  else k * binom M (lowMeanMassMode M n l h) (n : ℤ)

/-- The second bound in equation r12:eq53 on the binomial support. -/
theorem lowMean_kernel_second_lower {M n : ℕ} (hn : n ≤ M)
    {l h q wL wR : ℝ} (hwL : 0 ≤ wL) (hwR : 0 ≤ wR)
    (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h) :
    lowMeanKernelL M n
      (wL * (((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n)))
      (wR * ((2 * (n : ℝ) + 1 - M) / ((n : ℝ) + 1))) l h ≤
        kernel2 q wL wR M (n : ℤ) := by
  have hnR : (n : ℝ) ≤ M := by exact_mod_cast hn
  have hq0 := lt_of_lt_of_le hl hq.1
  have hq1 := lt_of_le_of_lt hq.2 hh
  let a := wL * (((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n))
  let b := wR * ((2 * (n : ℝ) + 1 - M) / ((n : ℝ) + 1))
  have hab : 0 ≤ a ∨ 0 ≤ b := by
    rcases le_total (2 * (n : ℝ)) ((M : ℝ) + 1) with ha | ha
    · left; exact mul_nonneg hwL (div_nonneg (by linarith) (by linarith))
    · right; exact mul_nonneg hwR (div_nonneg (by linarith) (by positivity))
  have hk := lowMean_multiplier_lower hab hl hh hq
  have hb0 := lowMean_binom_nonneg M n hq0.le hq1.le
  have he : kernel2 q wL wR M (n : ℤ) =
      lowMeanMultiplier a b q * binom M q (n : ℤ) := by
    rw [kernel2, lowMean_fL_factor hn, lowMean_fR_factor hn]
    unfold lowMeanMultiplier a b
    ring
  rw [he]
  change lowMeanKernelL M n a b l h ≤ _
  unfold lowMeanKernelL
  dsimp only
  split_ifs with hk0
  · exact le_trans (mul_le_mul_of_nonneg_left (lowMean_binom_endpoint_min hn hl hh hq) hk0)
      (mul_le_mul_of_nonneg_right hk hb0)
  · exact le_trans (mul_le_mul_of_nonpos_left (lowMean_binom_clipped_max hn hl hh hq)
      (le_of_not_ge hk0)) (mul_le_mul_of_nonneg_right hk hb0)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_binom_endpoint_min
#print axioms Erdos993Lean.Analytic.V213.lowMean_binom_clipped_max
#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_second_lower
