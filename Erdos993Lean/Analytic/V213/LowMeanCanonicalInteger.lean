module

public import Erdos993Lean.Analytic.V213.LowMeanTermBindings

/-!
Canonical kernel coefficients as explicit Int/Nat fractions. These
coefficients are derived from binomial coefficients and the printed weights,
not copied from the generated support records. Combined-term checks can
therefore discharge the whole-function kernel identity.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def lowMeanIntegerCoeffL (M n : ℕ) (wL : lowMeanFraction) : lowMeanFraction :=
  lowMeanFractionMul (lowMeanFractionMul wL (M.choose n, 1))
    ((M : ℤ) + 1 - 2 * n, M + 1 - n)
def lowMeanIntegerCoeffR (M n : ℕ) (wR : lowMeanFraction) : lowMeanFraction :=
  lowMeanFractionMul (lowMeanFractionMul wR (M.choose n, 1))
    (2 * (n : ℤ) + 1 - M, n + 1)
def lowMeanCanonicalIntegerTerms (M : ℕ) (j : ℤ) (wL wR z : lowMeanFraction) : List lowMeanIntegerTerm :=
  if j = -1 then [(lowMeanFractionNeg wR, 0, (M : ℤ)), (z, 0, (M : ℤ))]
  else if j = (M : ℤ) + 1 then [(lowMeanFractionNeg wL, (M : ℤ), 0), (z, 0, (M : ℤ))]
  else if 0 ≤ j ∧ j ≤ M then
    [(lowMeanIntegerCoeffL M j.toNat wL, j - 1, (M : ℤ) - j + 1),
      (lowMeanIntegerCoeffR M j.toNat wR, j + 1, (M : ℤ) - j - 1), (z, 0, (M : ℤ))]
  else [(z, 0, (M : ℤ))]

@[simp] theorem lowMean_integerCoeffL_real (M n : ℕ) (hn : n ≤ M) (wL : lowMeanFraction) :
    lowMeanFractionReal (lowMeanIntegerCoeffL M n wL) = lowMeanCoeffL M n (lowMeanFractionReal wL) := by
  unfold lowMeanIntegerCoeffL
  rw [lowMean_fraction_mul, lowMean_fraction_mul]
  simp [lowMeanFractionReal, lowMeanCoeffL, Nat.cast_sub (by omega : n ≤ M + 1)]
@[simp] theorem lowMean_integerCoeffR_real (M n : ℕ) (wR : lowMeanFraction) :
    lowMeanFractionReal (lowMeanIntegerCoeffR M n wR) = lowMeanCoeffR M n (lowMeanFractionReal wR) := by
  unfold lowMeanIntegerCoeffR
  rw [lowMean_fraction_mul, lowMean_fraction_mul]
  simp [lowMeanFractionReal, lowMeanCoeffR]

theorem lowMean_canonicalInteger_real (M : ℕ) (j : ℤ) (wL wR z : lowMeanFraction) :
    lowMeanIntegerTermsReal (lowMeanCanonicalIntegerTerms M j wL wR z) =
      lowMeanCanonicalTerms M j (lowMeanFractionReal wL) (lowMeanFractionReal wR) (lowMeanFractionReal z) := by
  unfold lowMeanCanonicalIntegerTerms lowMeanCanonicalTerms lowMeanIntegerTermsReal
  split_ifs with hjneg hjtop hj
  · simp [lowMean_fraction_neg]
  · simp [lowMean_fraction_neg]
  · have hn : j.toNat ≤ M := by omega
    simp [lowMean_integerCoeffL_real M j.toNat hn]
  · simp

/-- A generic integer binding check entails the actual kernel identity at
all real probabilities in (0,1), including boundary ranks and zero weights. -/
theorem lowMean_canonicalInteger_binding (M : ℕ) (j : ℤ) (wL wR z : lowMeanFraction)
    (terms : List lowMeanIntegerTerm)
    (h : lowMeanIntegerBindingCheck (lowMeanCanonicalIntegerTerms M j wL wR z) terms = true)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    kernel2 q (lowMeanFractionReal wL) (lowMeanFractionReal wR) M j + lowMeanFractionReal z * (1 - q) ^ M =
      ((lowMeanIntegerTermsReal terms).map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum := by
  have hi := lowMean_integerBinding_identity (lowMeanCanonicalIntegerTerms M j wL wR z) terms h q
  rw [lowMean_canonicalInteger_real, lowMean_canonical_identity M j hq0 hq1] at hi
  exact hi

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_canonicalInteger_binding
