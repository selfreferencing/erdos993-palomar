module

public import Erdos993Lean.Analytic.V213.LowMeanMass

/-!
The negative-kernel maximum in Lemma 6.5 of version 2.13 of the manuscript (`r12:lem12`).
The probability monotonicity proof
uses the paper's adjacent-rank comparison at n/M and induction on rank,
so it does not need to differentiate a maximum across branch crossings.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- The function g_J printed in Lemma 6.5. -/
noncomputable def lowMeanG (M n : ℕ) (q : ℝ) : ℝ :=
  ((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n) * binom M q (n : ℤ)

theorem lowMeanG_nonneg {M n : ℕ} (hn : 2 * n ≤ M) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 ≤ lowMeanG M n q := by
  have hnR : 2 * (n : ℝ) ≤ M := by exact_mod_cast hn
  unfold lowMeanG
  exact mul_nonneg (div_nonneg (by linarith) (by linarith))
    (lowMean_binom_nonneg M n hq0 hq1)

theorem lowMeanG_zero (M : ℕ) (q : ℝ) : lowMeanG M 0 q = (1 - q) ^ M := by
  have hden : (M : ℝ) + 1 ≠ 0 := by positivity
  simp only [lowMeanG, Nat.cast_zero, mul_zero, sub_zero, div_self hden, one_mul]
  change binom M q ((0 : ℕ) : ℤ) = _
  rw [binom_nat]
  simp

/-- Multiplication by the positive rank coefficient preserves mass monotonicity. -/
theorem lowMeanG_antitone {M n : ℕ} (hn : 2 * n ≤ M) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hmode : (n : ℝ) ≤ M * a) :
    AntitoneOn (lowMeanG M n) (Set.Icc a b) := by
  have hnR : 2 * (n : ℝ) ≤ M := by exact_mod_cast hn
  have hc : 0 ≤ ((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n) :=
    div_nonneg (by linarith) (by linarith)
  intro q hq s hs hqs
  exact mul_le_mul_of_nonneg_left
    (lowMean_binom_antitone (by omega : n ≤ M) ha hb hmode hq hs hqs) hc

/-- The paper's successive-ratio identity, with its denominators cleared. -/
theorem lowMeanG_adjacent {M n : ℕ} (hn : n < M) (q : ℝ) :
    ((M : ℝ) + 1 - 2 * n) * ((n : ℝ) + 1) * (1 - q) * lowMeanG M (n + 1) q =
      ((M : ℝ) - 1 - 2 * n) * ((M : ℝ) + 1 - n) * q * lowMeanG M n q := by
  have hnR : (n : ℝ) < M := by exact_mod_cast hn
  have hden1 : (M : ℝ) - n ≠ 0 := by linarith
  have hden0 : (M : ℝ) + 1 - n ≠ 0 := by linarith
  have hg1 : ((M : ℝ) - n) * lowMeanG M (n + 1) q =
      ((M : ℝ) - 1 - 2 * n) * binom M q ((n + 1 : ℕ) : ℤ) := by
    unfold lowMeanG
    push_cast
    have he : (M : ℝ) + 1 - ((n : ℝ) + 1) = (M : ℝ) - n := by ring
    rw [he]
    field_simp
    ring
  have hg0 : ((M : ℝ) + 1 - n) * lowMeanG M n q =
      ((M : ℝ) + 1 - 2 * n) * binom M q (n : ℤ) := by
    unfold lowMeanG
    field_simp
  have hb := lowMean_binom_adjacent hn q
  apply mul_left_cancel₀ hden1
  linear_combination
    (((M : ℝ) + 1 - 2 * n) * ((n : ℝ) + 1) * (1 - q)) * hg1 -
    (((M : ℝ) - n) * ((M : ℝ) - 1 - 2 * n) * q) * hg0 +
    (((M : ℝ) + 1 - 2 * n) * ((M : ℝ) - 1 - 2 * n)) * hb

/-- To the left of the new rank's mode, the previous rank dominates it. -/
theorem lowMeanG_le_previous {M n : ℕ} (hn : 2 * (n + 1) ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmode : (M : ℝ) * q ≤ (n : ℝ) + 1) :
    lowMeanG M (n + 1) q ≤ lowMeanG M n q := by
  have hnR : 2 * ((n : ℝ) + 1) ≤ M := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hM : (0 : ℝ) < M := by linarith
  let A : ℝ := (M : ℝ) + 1 - 2 * n
  let A' : ℝ := (M : ℝ) - 1 - 2 * n
  let D : ℝ := A * ((n : ℝ) + 1) * (1 - q)
  let N : ℝ := A' * ((M : ℝ) + 1 - n) * q
  have hA : 0 < A := by dsimp [A]; linarith
  have hA' : 0 < A' := by dsimp [A']; linarith
  have hden : 0 < (M : ℝ) + 1 - n := by linarith
  have hD : 0 < D := mul_pos (mul_pos hA (by positivity)) (sub_pos.mpr hq1)
  have hc : 0 ≤ A' * ((M : ℝ) + 1 - n) + A * ((n : ℝ) + 1) := by
    positivity
  have hb := mul_le_mul_of_nonneg_left hmode hc
  have he : (M : ℝ) * (N - D) =
      (A' * ((M : ℝ) + 1 - n) + A * ((n : ℝ) + 1)) * ((M : ℝ) * q - ((n : ℝ) + 1)) -
        2 * n * ((n : ℝ) + 1) := by
    dsimp [A, A', N, D]
    ring
  have hND : N ≤ D := by nlinarith
  have hg0 := lowMeanG_nonneg (by omega : 2 * n ≤ M) hq0.le hq1.le
  have hmul := mul_le_mul_of_nonneg_right hND hg0
  have hadj := lowMeanG_adjacent (by omega : n < M) q
  change D * lowMeanG M (n + 1) q = N * lowMeanG M n q at hadj
  exact (mul_le_mul_iff_left₀ hD).mp (by linarith)

/-- A bound for every rank at l continues to hold for every larger q<1.
This proves the probability part of Lemma 6.5 without any branch regularity
assumption about the maximizing index. -/
theorem lowMeanG_uniform_bound {M : ℕ} {l q B : ℝ}
    (hl : 0 < l) (hlq : l ≤ q) (hq1 : q < 1)
    (hB : ∀ n : ℕ, 2 * n ≤ M → lowMeanG M n l ≤ B) :
    ∀ n : ℕ, 2 * n ≤ M → lowMeanG M n q ≤ B := by
  have main : ∀ n : ℕ, ∀ q : ℝ, l ≤ q → q < 1 → 2 * n ≤ M → lowMeanG M n q ≤ B := by
    intro n
    induction n with
    | zero =>
      intro q hlq hq1 _
      calc
        lowMeanG M 0 q = (1 - q) ^ M := lowMeanG_zero M q
        _ ≤ (1 - l) ^ M := pow_le_pow_left₀ (by linarith) (by linarith) M
        _ = lowMeanG M 0 l := (lowMeanG_zero M l).symm
        _ ≤ B := hB 0 (by omega)
    | succ n ih =>
      intro q hlq hq1 hn
      have hnR : 2 * ((n : ℝ) + 1) ≤ M := by exact_mod_cast hn
      have hM : (0 : ℝ) < M := by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
      have hq0 := lt_of_lt_of_le hl hlq
      by_cases hml : ((n : ℝ) + 1) ≤ M * l
      · exact le_trans
          (lowMeanG_antitone hn hl hq1 (by simpa using hml)
            (show l ∈ Set.Icc l q from ⟨le_rfl, hlq⟩)
            (show q ∈ Set.Icc l q from ⟨hlq, le_rfl⟩) hlq)
          (hB (n + 1) hn)
      · by_cases hmq : (M : ℝ) * q ≤ (n : ℝ) + 1
        · exact le_trans (lowMeanG_le_previous hn hq0 hq1 hmq) (ih q hlq hq1 (by omega))
        · let a : ℝ := ((n : ℝ) + 1) / M
          have ha : 0 < a := div_pos (by positivity) hM
          have hla : l ≤ a := (le_div_iff₀ hM).mpr (by linarith)
          have haq : a ≤ q := (div_le_iff₀ hM).mpr (by linarith)
          have ha1 : a < 1 := lt_of_le_of_lt haq hq1
          have he : (M : ℝ) * a = (n : ℝ) + 1 := by dsimp [a]; field_simp
          calc
            lowMeanG M (n + 1) q ≤ lowMeanG M (n + 1) a :=
              lowMeanG_antitone hn ha hq1 (by push_cast; linarith)
                ⟨le_rfl, haq⟩ ⟨haq, le_rfl⟩ haq
            _ ≤ lowMeanG M n a := lowMeanG_le_previous hn ha ha1 he.le
            _ ≤ B := ih a hla ha1 (by omega)
  exact fun n hn => main n q hlq hq1 hn

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanG_uniform_bound
