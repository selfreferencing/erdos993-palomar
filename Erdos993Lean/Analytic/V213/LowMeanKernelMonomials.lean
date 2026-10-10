module

public import Erdos993Lean.Analytic.V213.LowMeanKernelIdentities
public import Erdos993Lean.Analytic.V213.LowMeanMonomialSupport

/-!
Equation r12:eq55 and the semantic bridge from signed monomial
supports to the slack quadratic r12:eq58. The kernel identity is derived
from the definitions, including both negative boundary exponents.
No finite generated record is used in this module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoeffL (M n : ℕ) (wL : ℝ) : ℝ :=
  wL * (M.choose n : ℝ) * (((M : ℝ) + 1 - 2 * n) / ((M : ℝ) + 1 - n))
noncomputable def lowMeanCoeffR (M n : ℕ) (wR : ℝ) : ℝ :=
  wR * (M.choose n : ℝ) * ((2 * (n : ℝ) + 1 - M) / ((n : ℝ) + 1))

/-- The two monomials in r12:eq55, including n=0 and n=M. -/
theorem lowMean_kernel_monomials {M n : ℕ} (hn : n ≤ M) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (wL wR : ℝ) :
    kernel2 q wL wR M (n : ℤ) =
      lowMeanMonomial (lowMeanCoeffL M n wL) ((n : ℤ) - 1)
        (((M - n : ℕ) : ℤ) + 1) q +
      lowMeanMonomial (lowMeanCoeffR M n wR) ((n : ℤ) + 1)
        (((M - n : ℕ) : ℤ) - 1) q := by
  have hq : q ≠ 0 := hq0.ne'
  have h1 : 1 - q ≠ 0 := (sub_pos.mpr hq1).ne'
  rw [kernel2, lowMean_fL_factor hn, lowMean_fR_factor hn, binom_nat]
  unfold lowMeanMonomial lowMeanCoeffL lowMeanCoeffR
  rw [zpow_sub₀ hq, zpow_add₀ h1, zpow_add₀ hq, zpow_sub₀ h1]
  simp only [zpow_natCast, zpow_one]
  field_simp

/-- Summing termwise supports gives the exact slack lower budget. Zero
coefficients are discarded; the retained terms satisfy the printed signs
and exponent condition, rather than an assumed slack inequality. -/
theorem lowMean_slack_support
    (terms : List (ℝ × ℤ × ℤ))
    {M : ℕ} {j : ℤ} {q L H tau wL wR xi eta alpha beta gamma m0 z zeta : ℝ}
    (hL : 0 < L) (hH : H < 1) (hLH : L < H)
    (htau : tau ∈ Set.Icc L H) (hq : q ∈ Set.Icc L H)
    (hterms : ∀ t ∈ terms, t.1 ≠ 0 ∧ 0 ≤ t.2.1 + t.2.2)
    (hidentity : kernel2 q wL wR M j + z * (1 - q) ^ M =
      (terms.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum) :
    eta * ((j : ℝ) - M * q) ^ 2 + xi * ((j : ℝ) - M * q) -
        lowMeanPsi alpha beta gamma m0 M - zeta +
        (terms.map fun t => lowMeanSupport t.1 t.2.1 t.2.2 L H tau q).sum ≤
      lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M +
        z * (1 - q) ^ M - zeta := by
  have hs : (terms.map fun t => lowMeanSupport t.1 t.2.1 t.2.2 L H tau q).sum ≤
      (terms.map fun t => lowMeanMonomial t.1 t.2.1 t.2.2 q).sum := by
    apply List.sum_le_sum
    intro t ht
    exact lowMean_signedMonomial_support (hterms t ht).1 t.2.1 t.2.2
      (hterms t ht).2 hL hH hLH htau hq
  rw [← hidentity] at hs
  unfold lowMeanH
  linarith

/-- A positive exact quadratic minimum certifies the whole closed interval. -/
theorem lowMean_slack_positive_of_quadratic
    {M : ℕ} {j : ℤ} {L H A B C wL wR xi eta alpha beta gamma m0 z zeta : ℝ}
    (hLH : L < H)
    (hbudget : 0 < lowMeanQuadMinimum A B C L H)
    (hsupport : ∀ q ∈ Set.Icc L H,
      lowMeanQuad A B C q ≤
        lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M +
          z * (1 - q) ^ M - zeta)
    {q : ℝ} (hq : q ∈ Set.Icc L H) :
    zeta < lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M +
      z * (1 - q) ^ M := by
  have hmin := lowMeanQuadMinimum_le (A := A) (B := B) (C := C) hLH hq
  have hs := hsupport q hq
  linarith

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_kernel_monomials
#print axioms Erdos993Lean.Analytic.V213.lowMean_slack_support
#print axioms Erdos993Lean.Analytic.V213.lowMean_slack_positive_of_quadratic
