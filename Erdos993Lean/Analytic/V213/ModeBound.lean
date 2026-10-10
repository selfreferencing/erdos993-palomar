module

public import Erdos993Lean.Analytic.V213.Foundation
public import Erdos993Lean.Ceiling.Join

/-!
The elementary log-concavity-to-mode step in the proof of Lemma2.1.
Its precise hypotheses are positivity through D and zero extension after D.
There is no assertion that a general log-concave law has its mode near its mean.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- Once adjacent coefficients cease rising, log-concavity and positive support
force all later coefficients to be nonincreasing. -/
theorem antitone_from_descent {b : ℕ → ℕ} {D k : ℕ}
    (hlc : LogConcave b) (hpos : Ceiling.PosUpTo b D)
    (hdescent : b (k + 1) ≤ b k) :
    ∀ j : ℕ, k ≤ j → b (j + 1) ≤ b j := by
  intro j hkj
  induction j, hkj using Nat.le_induction with
  | base => exact hdescent
  | succ j hkj ih =>
    rcases Nat.eq_zero_or_pos (b (j + 1)) with hzero | hpositive
    · have hDj : D < j + 1 := by
        by_contra h
        have hp := hpos.1 (j + 1) (by omega)
        omega
      rw [hpos.2 (j + 1 + 1) (by omega)]
      exact Nat.zero_le _
    · have hjpositive : 0 < b j := lt_of_lt_of_le hpositive ih
      have h1 := hlc j
      have h2 := Nat.mul_le_mul_right (b (j + 1)) ih
      apply Nat.le_of_mul_le_mul_left _ hjpositive
      exact le_trans h1 h2

/-- The first mode is at or before a weak adjacent descent, including ties. -/
theorem firstMode_le_at_descent {b : ℕ → ℕ} {D k : ℕ}
    (hlc : LogConcave b) (hpos : Ceiling.PosUpTo b D)
    (hdescent : b (k + 1) ≤ b k) : firstMode b ≤ k := by
  exact Join.firstMode_le_of_antitone_from (antitone_from_descent hlc hpos hdescent)

/-- The exact positive support and log-concavity of the printed matching row. -/
theorem matchingRow_logConcave_positive (n ν : ℕ) :
    LogConcave (bRow n ν) ∧ Ceiling.PosUpTo (bRow n ν) (ν + (n - 2 * ν)) :=
  Ceiling.bRow_good n ν

/-- Source specialization of the mode step; it also includes n=ν=0. -/
theorem matchingRow_firstMode_le_at_descent (n ν k : ℕ)
    (hdescent : bRow n ν (k + 1) ≤ bRow n ν k) :
    firstMode (bRow n ν) ≤ k := by
  exact firstMode_le_at_descent (matchingRow_logConcave_positive n ν).1
    (matchingRow_logConcave_positive n ν).2 hdescent

end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.antitone_from_descent
#print axioms Erdos993Lean.Analytic.V213.antitone_from_descent
#check Erdos993Lean.Analytic.V213.firstMode_le_at_descent
#print axioms Erdos993Lean.Analytic.V213.firstMode_le_at_descent
#check Erdos993Lean.Analytic.V213.matchingRow_logConcave_positive
#print axioms Erdos993Lean.Analytic.V213.matchingRow_logConcave_positive
#check Erdos993Lean.Analytic.V213.matchingRow_firstMode_le_at_descent
#print axioms Erdos993Lean.Analytic.V213.matchingRow_firstMode_le_at_descent
