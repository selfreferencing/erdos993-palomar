module

public import Erdos993Lean.Analytic.V213.LowMeanHeat

/-!
Lemma 6.1 of version 2.13 of the manuscript (`r12:lem9`), priced-seed tail propagation.
A scalar upper bound on q(1-q)
is sufficient; taking the maximum on the printed interval gives v_Q.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- Iterated heat averaging preserves a uniform lower bound, paying at most
eta*v per step. The bound covers every integer rank after convolution. -/
theorem lowMeanH_iterate
    {q wL wR xi eta v B : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (heta : 0 ≤ eta) (hv : q * (1 - q) ≤ v) (T k : ℕ)
    (hseed : ∀ j : ℤ, B ≤ lowMeanH q wL wR xi eta T j) :
    ∀ j : ℤ, B - (k : ℝ) * eta * v ≤ lowMeanH q wL wR xi eta (T + k) j := by
  induction k with
  | zero => simpa using hseed
  | succ k ih =>
    intro j
    have hleft := mul_le_mul_of_nonneg_left (ih (j - 1)) hq0
    have hright := mul_le_mul_of_nonneg_left (ih j) (sub_nonneg.mpr hq1)
    have hcost := mul_le_mul_of_nonneg_left hv heta
    rw [show T + k.succ = (T + k) + 1 by omega, lowMeanH_heat]
    push_cast
    nlinarith

/-- The exact algebraic remainder used to discharge the tail. -/
theorem lowMean_tail_remainder (alpha beta gamma m0 T k eta v C : ℝ) :
    lowMeanPsi alpha beta gamma m0 T - C - k * eta * v -
        lowMeanPsi alpha beta gamma m0 (T + k) =
      k * (2 * gamma * (T - m0) + gamma - beta - eta * v - C) +
        (k - 1) * C + gamma * k * (k - 1) := by
  unfold lowMeanPsi
  ring

/-- Lemma 6.1, tail conclusion: one priced seed and a nonnegative discharge
budget imply an unpriced bound at every width strictly above T.
This pointwise form applies to every q in the paper's closed interval. -/
theorem lowMean_tail
    {q l wL wR xi eta alpha beta gamma m0 z0 v eps : ℝ}
    {T M : ℕ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hlq : l ≤ q)
    (heta : 0 ≤ eta) (hgamma : 0 ≤ gamma) (hz0 : 0 ≤ z0)
    (hv : q * (1 - q) ≤ v)
    (hbudget : 0 ≤ 2 * gamma * ((T : ℝ) - m0) + gamma - beta -
      eta * v - z0 * (1 - l) ^ T)
    (hseed : ∀ j : ℤ,
      lowMeanPsi alpha beta gamma m0 T - z0 * (1 - q) ^ T + eps ≤
        lowMeanH q wL wR xi eta T j)
    (hTM : T < M) (j : ℤ) :
    lowMeanPsi alpha beta gamma m0 M + eps ≤ lowMeanH q wL wR xi eta M j := by
  let C := z0 * (1 - l) ^ T
  have hC : 0 ≤ C := mul_nonneg hz0 (pow_nonneg (by linarith) _)
  have hprice : z0 * (1 - q) ^ T ≤ C :=
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sub_nonneg.mpr hq1) (by linarith : 1 - q ≤ 1 - l) T) hz0
  have hseed' : ∀ j : ℤ,
      lowMeanPsi alpha beta gamma m0 T - C + eps ≤ lowMeanH q wL wR xi eta T j := by
    intro j
    linarith [hseed j]
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt hTM)
  have hk : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hiter := lowMeanH_iterate hq0 hq1 heta hv T k hseed' j
  have hd := mul_nonneg (by linarith : 0 ≤ (k : ℝ)) hbudget
  have hremC := mul_nonneg (by linarith : 0 ≤ (k : ℝ) - 1) hC
  have hremG := mul_nonneg
    (mul_nonneg hgamma (by linarith : 0 ≤ (k : ℝ))) (by linarith : 0 ≤ (k : ℝ) - 1)
  have hid := lowMean_tail_remainder alpha beta gamma m0 T k eta v C
  change 0 ≤ (k : ℝ) *
    (2 * gamma * ((T : ℝ) - m0) + gamma - beta - eta * v - C) at hd
  push_cast at hiter ⊢
  linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanH_iterate
#print axioms Erdos993Lean.Analytic.V213.lowMean_tail_remainder
#print axioms Erdos993Lean.Analytic.V213.lowMean_tail
