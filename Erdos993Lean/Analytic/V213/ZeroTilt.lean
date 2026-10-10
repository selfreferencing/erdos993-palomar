module

public import Erdos993Lean.Analytic.MGF.Criterion

/-!
Paper-facing specialization of Lemma 2.6 of version 2.13 of the manuscript (r12:lem5).
One zero-tilt price is retained.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- The printed zero-tilt criterion, for an arbitrary finite probability mixture.
The real parameters beta and xi are unrestricted; no positivity of mu, theta,
D or ell is added to the paper's assumptions. -/
theorem zeroTilt_noValley
    {ι : Type} (X : Mixture ι) (k : ℤ)
    {q mu theta D ell eta xi alpha beta gamma wL wR z0 : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (heta : 0 < eta)
    (hgamma : 0 ≤ gamma) (hwL : 0 ≤ wL) (hwR : 0 ≤ wR)
    (hz0 : 0 ≤ z0)
    (hpoint : ∀ (M : ℕ) (j : ℤ),
      alpha + beta * ((M : ℝ) - mu) - gamma * ((M : ℝ) - mu) ^ 2 -
        z0 * (1 - q) ^ M ≤
      kernel2 q wL wR M j + xi * ((j : ℝ) - q * M) +
        eta * ((j : ℝ) - q * M) ^ 2)
    (hmargin : 0 < alpha - gamma * D * mu - z0 * Real.exp (-ell * mu) -
      eta * theta * q * (1 - q) * mu)
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤
      theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-ell * mu)) :
    ¬ X.WeakValley q k := by
  have hcert : ExplicitThresholdMGF2 q mu theta D
      [(1 - q, Real.exp (-ell * mu))] := by
    refine ⟨eta, xi, alpha, beta, gamma, wL, wR, [z0],
      heta, hgamma, hwL, hwR, ?_, ?_, ?_⟩
    · simpa using hz0
    · intro M j
      simpa [pricedTail] using hpoint M j
    · simp only [pricedMargin]
      nlinarith [hmargin]
  apply noValleyAtMGF2_of_explicit hq0 hq1 hcert ι X k
    hX hmean hdelta hdelta2 hvar
  simpa using htail

end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.zeroTilt_noValley
#print axioms Erdos993Lean.Analytic.V213.zeroTilt_noValley

