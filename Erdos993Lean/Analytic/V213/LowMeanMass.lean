module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
Elementary mass and derivative identities for Lemma 6.5 of version 2.13 of the manuscript.
All proofs use the existing binomial definition. These identities also expose
the boundary cases needed by the later signed-monomial representation.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_binom_nonneg (M n : ℕ) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ binom M q (n : ℤ) := by
  rw [binom_nat]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hq0 _))
    (pow_nonneg (sub_nonneg.mpr hq1) _)

theorem lowMean_binom_pos {M n : ℕ} (hn : n ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) : 0 < binom M q (n : ℤ) := by
  rw [binom_nat]
  have hc : (0 : ℝ) < M.choose n := by exact_mod_cast Nat.choose_pos hn
  exact mul_pos (mul_pos hc (pow_pos hq0 _)) (pow_pos (sub_pos.mpr hq1) _)

/-- The adjacent-rank relation, with no divisions or probability restrictions. -/
theorem lowMean_binom_adjacent {M n : ℕ} (hn : n < M) (q : ℝ) :
    ((n : ℝ) + 1) * (1 - q) * binom M q ((n + 1 : ℕ) : ℤ) =
      ((M : ℝ) - n) * q * binom M q (n : ℤ) := by
  have hc := congrArg (fun x : ℕ => (x : ℝ)) (Nat.choose_succ_right_eq M n)
  push_cast at hc
  rw [Nat.cast_sub hn.le] at hc
  rw [binom_nat, binom_nat, show M - n = M - (n + 1) + 1 by omega]
  simp only [pow_succ]
  linear_combination (q ^ n * (1 - q) ^ (M - (n + 1)) * q * (1 - q)) * hc

theorem lowMean_nat_mul_pow_pred (n : ℕ) (x : ℝ) :
    (n : ℝ) * x ^ (n - 1) * x = (n : ℝ) * x ^ n := by
  cases n with
  | zero => simp
  | succ n => simp only [Nat.add_sub_cancel, pow_succ]; ring

/-- The binomial mass derivative on (0,1), including ranks 0 and M. -/
theorem lowMean_binom_hasDerivAt {M n : ℕ} (hn : n ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => binom M x (n : ℤ))
      (binom M q (n : ℤ) * ((n : ℝ) - M * q) / (q * (1 - q))) q := by
  have hfun : (fun x : ℝ => binom M x (n : ℤ)) =
      fun x : ℝ => (M.choose n : ℝ) * x ^ n * (1 - x) ^ (M - n) := by
    funext x
    exact binom_nat M n x
  have hd := ((hasDerivAt_pow n q).const_mul (M.choose n : ℝ)).mul
    (((hasDerivAt_id q).const_sub 1).pow (M - n))
  have he1 := lowMean_nat_mul_pow_pred n q
  have he2 := lowMean_nat_mul_pow_pred (M - n) (1 - q)
  have hden : q * (1 - q) ≠ 0 := mul_ne_zero hq0.ne' (sub_pos.mpr hq1).ne'
  rw [hfun]
  convert hd using 1
  · rfl
  · symm
    rw [binom_nat]
    apply (eq_div_iff hden).2
    rw [Nat.cast_sub hn] at he2 ⊢
    simp only [Pi.pow_apply, id_eq]
    linear_combination
      ((M.choose n : ℝ) * (1 - q) ^ (M - n) * (1 - q)) * he1 -
      ((M.choose n : ℝ) * q ^ n * q) * he2

/-- A binomial mass is nonincreasing to the right of its mode n/M.
The division-free hypothesis also covers M=0. -/
theorem lowMean_binom_antitone {M n : ℕ} (hn : n ≤ M) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hmode : (n : ℝ) ≤ M * a) :
    AntitoneOn (fun q : ℝ => binom M q (n : ℤ)) (Set.Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
    (by simpa only [binom_nat] using
      (show ContinuousOn (fun x : ℝ => (M.choose n : ℝ) * x ^ n * (1 - x) ^ (M - n))
        (Set.Icc a b) by fun_prop))
    (fun q hq => (lowMean_binom_hasDerivAt hn
      (lt_of_lt_of_le ha (interior_subset hq).1)
      (lt_of_le_of_lt (interior_subset hq).2 hb)).hasDerivWithinAt)
  intro q hq
  have hq' : q ∈ Set.Icc a b := interior_subset hq
  have hq0 := lt_of_lt_of_le ha hq'.1
  have hq1 := lt_of_le_of_lt hq'.2 hb
  have hMq := mul_le_mul_of_nonneg_left hq'.1 (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (lowMean_binom_nonneg M n hq0.le hq1.le) (by linarith))
    (mul_nonneg hq0.le (sub_nonneg.mpr hq1.le))

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_binom_adjacent
#print axioms Erdos993Lean.Analytic.V213.lowMean_binom_hasDerivAt
#print axioms Erdos993Lean.Analytic.V213.lowMean_binom_antitone
