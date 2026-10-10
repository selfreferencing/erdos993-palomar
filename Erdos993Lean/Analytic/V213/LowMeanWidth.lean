module

public import Erdos993Lean.Analytic.V213.LowMeanTail

/-!
Strong-seed propagation, Lemma 6.4 of version 2.13 of the manuscript (`r12:lem11`).
The price difference is controlled
uniformly in q before iterating the heat bound; the minimizing rank is never
held fixed during convolution.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- An elementary form of the Bernoulli estimate used in the width proof. -/
theorem lowMean_pow_decay {x t : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hstep : (t + 1) * x ≤ t) (k : ℕ) : (t + k) * x ^ k ≤ t := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hmul := mul_le_mul_of_nonneg_right ih hx0
    have hp := pow_le_one₀ (n := k) hx0 hx1
    have hpx := mul_le_mul_of_nonneg_right hp hx0
    rw [pow_succ]
    push_cast
    nlinarith

/-- The price lost between widths t and t+k is largest at the left
probability endpoint when t ≥ (1-l)/l. -/
theorem lowMean_price_difference_antitone
    {l h : ℝ} (hl : 0 < l) (hh : h < 1) (t k : ℕ)
    (ht : (1 - l) / l ≤ (t : ℝ)) :
    AntitoneOn (fun q : ℝ => (1 - q) ^ t - (1 - q) ^ (t + k)) (Set.Icc l h) := by
  by_cases hle : l ≤ h
  · have htpos : 1 ≤ t := by
      have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le (div_pos (by linarith) hl) ht
      exact_mod_cast (show (0 : ℝ) < t from ht0)
    have hderiv (q : ℝ) :
        HasDerivAt (fun q : ℝ => (1 - q) ^ t - (1 - q) ^ (t + k))
          ((t : ℝ) * (1 - q) ^ (t - 1) * (-1) -
            ((t + k : ℕ) : ℝ) * (1 - q) ^ (t + k - 1) * (-1)) q := by
      convert (((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).pow t).sub
        (((hasDerivAt_const q (1 : ℝ)).sub (hasDerivAt_id q)).pow (t + k)) using 1
      · rfl
      · norm_num
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc l h)
      (by fun_prop) (fun q _ => (hderiv q).hasDerivWithinAt)
    intro q hq
    have hq' : q ∈ Set.Icc l h := interior_subset hq
    have hx0 : 0 ≤ 1 - q := by linarith [hq'.2]
    have hx1 : 1 - q ≤ 1 := by linarith [hq'.1]
    have htl := (div_le_iff₀ hl).mp ht
    have hstep : ((t : ℝ) + 1) * (1 - q) ≤ t := by
      have he := mul_le_mul_of_nonneg_left hq'.1
        (by positivity : 0 ≤ (t : ℝ) + 1)
      nlinarith
    have hd := lowMean_pow_decay hx0 hx1 hstep k
    have hm := mul_le_mul_of_nonneg_left hd (pow_nonneg hx0 (t - 1))
    rw [show t + k - 1 = (t - 1) + k by omega, pow_add]
    push_cast
    nlinarith
  · intro a ha b hb _
    exact (hle (le_trans ha.1 ha.2)).elim

/-- The auxiliary potential in Lemma 6.4. -/
def lowMeanV (alpha beta gamma m0 eta v z0 l : ℝ) (m : ℕ) : ℝ :=
  lowMeanPsi alpha beta gamma m0 m + eta * v * m - z0 * (1 - l) ^ m

theorem lowMeanV_step (alpha beta gamma m0 eta v z0 l : ℝ) (m : ℕ) :
    lowMeanV alpha beta gamma m0 eta v z0 l (m + 1) -
        lowMeanV alpha beta gamma m0 eta v z0 l m =
      beta + gamma + eta * v - 2 * gamma * ((m + 1 : ℕ) - m0) +
        z0 * l * (1 - l) ^ m := by
  unfold lowMeanV lowMeanPsi
  rw [pow_succ]
  push_cast
  ring

/-- The printed slope condition makes the potential nondecreasing through r. -/
theorem lowMeanV_monotone
    {alpha beta gamma m0 eta v z0 l : ℝ} (r : ℕ)
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hgamma : 0 ≤ gamma) (hz0 : 0 ≤ z0)
    (hslope : 2 * gamma * ((r : ℝ) - m0) ≤ beta + gamma + eta * v) :
    MonotoneOn (lowMeanV alpha beta gamma m0 eta v z0 l) (Set.Iic r) := by
  apply monotoneOn_of_le_succ Set.ordConnected_Iic
  intro m _ _ hmr
  have hmr' : (m + 1 : ℝ) ≤ r := by exact_mod_cast hmr
  have hm := mul_le_mul_of_nonneg_left hmr' (by positivity : 0 ≤ 2 * gamma)
  have hp := mul_nonneg (mul_nonneg hz0 hl0) (pow_nonneg (sub_nonneg.mpr hl1) m)
  have he := lowMeanV_step alpha beta gamma m0 eta v z0 l m
  push_cast at he
  change lowMeanV alpha beta gamma m0 eta v z0 l m ≤
    lowMeanV alpha beta gamma m0 eta v z0 l (m + 1)
  linarith

/-- Lemma 6.4: the stronger seed fills every integer width in [t,r].
All probability endpoints and both width endpoints are included. -/
theorem lowMean_strongSeed
    {q l h wL wR xi eta alpha beta gamma m0 z0 v eps : ℝ}
    {t r m : ℕ} (hl : 0 < l) (hh : h < 1) (hq : q ∈ Set.Icc l h)
    (heta : 0 ≤ eta) (hgamma : 0 ≤ gamma) (hz0 : 0 ≤ z0)
    (hv : q * (1 - q) ≤ v) (_htr : t < r)
    (ht : (1 - l) / l ≤ (t : ℝ))
    (hslope : 2 * gamma * ((r : ℝ) - m0) ≤ beta + gamma + eta * v)
    (hseed : ∀ j : ℤ,
      eps + lowMeanV alpha beta gamma m0 eta v z0 l r -
          lowMeanV alpha beta gamma m0 eta v z0 l t ≤
        lowMeanH q wL wR xi eta t j - lowMeanPsi alpha beta gamma m0 t +
          z0 * (1 - q) ^ t)
    (htm : t ≤ m) (hmr : m ≤ r) (j : ℤ) :
    eps ≤ lowMeanH q wL wR xi eta m j - lowMeanPsi alpha beta gamma m0 m +
      z0 * (1 - q) ^ m := by
  have hq0 : 0 ≤ q := le_trans hl.le hq.1
  have hq1 : q ≤ 1 := le_trans hq.2 hh.le
  have hlh : l ≤ h := le_trans hq.1 hq.2
  have hseed' : ∀ j : ℤ,
      eps + lowMeanV alpha beta gamma m0 eta v z0 l r -
          lowMeanV alpha beta gamma m0 eta v z0 l t +
          lowMeanPsi alpha beta gamma m0 t - z0 * (1 - q) ^ t ≤
        lowMeanH q wL wR xi eta t j := by
    intro j
    linarith [hseed j]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htm
  have hi := lowMeanH_iterate hq0 hq1 heta hv t k hseed' j
  have hd := lowMean_price_difference_antitone hl hh t k ht
    (show l ∈ Set.Icc l h from ⟨le_rfl, hlh⟩) hq hq.1
  have hzd := mul_le_mul_of_nonneg_left hd hz0
  have hV := lowMeanV_monotone (alpha := alpha) r hl.le (le_trans hlh hh.le) hgamma hz0 hslope
    (show t + k ∈ Set.Iic r from hmr) (by simp : r ∈ Set.Iic r) hmr
  unfold lowMeanV at hi hV
  push_cast at hi hV ⊢
  nlinarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_price_difference_antitone
#print axioms Erdos993Lean.Analytic.V213.lowMeanV_monotone
#print axioms Erdos993Lean.Analytic.V213.lowMean_strongSeed
