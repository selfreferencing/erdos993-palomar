module

public import Erdos993Lean.Analytic.V213.LowMeanTail
public import Erdos993Lean.Analytic.V213.ZeroTilt

/-!
The generic low-mean mixture interface used in Theorem 6.2 of version 2.13 of the manuscript
(`r12:thm6`).
The printed seed and strict mean inequalities remain hypotheses of this
conditional theorem. This file does not claim that any table certificate
satisfies those inequalities; that is the later finite-data work.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- Recentring the quadratic at the actual mean changes neither polynomial. -/
theorem lowMeanPsi_recenter (alpha beta gamma m0 mu M : ℝ) :
    lowMeanPsi alpha beta gamma m0 mu +
        (beta - 2 * gamma * (mu - m0)) * (M - mu) - gamma * (M - mu) ^ 2 =
      lowMeanPsi alpha beta gamma m0 M := by
  unfold lowMeanPsi
  ring

/-- The conditional synthesis argument of Theorem 6.2 at one probability and
mean: a seed through T, a discharge budget, and the strict average margin
exclude a weak valley for every probability mixture with the printed moments. -/
theorem lowMean_noValley
    {ι : Type} (X : Mixture ι) (k : ℤ)
    {q l mu theta D ell eta xi alpha beta gamma m0 wL wR z0 v : ℝ}
    (T : ℕ) (hq0 : 0 < q) (hq1 : q < 1) (hlq : l ≤ q)
    (heta : 0 < eta) (hgamma : 0 ≤ gamma) (hwL : 0 ≤ wL) (hwR : 0 ≤ wR)
    (hz0 : 0 ≤ z0) (hv : q * (1 - q) ≤ v)
    (hbudget : 0 ≤ 2 * gamma * ((T : ℝ) - m0) + gamma - beta -
      eta * v - z0 * (1 - l) ^ T)
    (hseed : ∀ M : ℕ, M ≤ T → ∀ j : ℤ,
      0 ≤ lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M +
        z0 * (1 - q) ^ M)
    (hmargin : 0 < lowMeanPsi alpha beta gamma m0 mu - gamma * D * mu -
      eta * theta * q * (1 - q) * mu - z0 * Real.exp (-ell * mu))
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤
      theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-ell * mu)) :
    ¬ X.WeakValley q k := by
  apply zeroTilt_noValley X k hq0 hq1 heta hgamma hwL hwR hz0
    (alpha := lowMeanPsi alpha beta gamma m0 mu)
    (beta := beta - 2 * gamma * (mu - m0))
    (xi := xi) (ell := ell) (D := D) (theta := theta)
    ?_ ?_ hX hmean hdelta hvar hdelta2 htail
  · intro M j
    rw [lowMeanPsi_recenter]
    change lowMeanPsi alpha beta gamma m0 M - z0 * (1 - q) ^ M ≤
      lowMeanH q wL wR xi eta M j
    by_cases hMT : M ≤ T
    · linarith [hseed M hMT j]
    · have htseed : ∀ j : ℤ,
          lowMeanPsi alpha beta gamma m0 T - z0 * (1 - q) ^ T + 0 ≤
            lowMeanH q wL wR xi eta T j := by
        intro j
        linarith [hseed T le_rfl j]
      have ht := lowMean_tail hq0.le hq1.le hlq heta.le hgamma hz0 hv
        hbudget htseed (Nat.lt_of_not_ge hMT) j
      have hp := mul_nonneg hz0 (pow_nonneg (sub_nonneg.mpr hq1.le) M)
      linarith
  · linarith [hmargin]

/-- The same conditional synthesis on the paper's exact closed natural mean
domain max(mu_a,4/q) ≤ mu ≤ mu_b. Group maxima and the rate function are
parameters; their identification with the printed data is made in a later module. -/
theorem lowMean_noValley_on_domain
    {ι : Type} (X : Mixture ι) (k : ℤ)
    {l h muA muB theta D eta xi alpha beta gamma m0 wL wR z0 v : ℝ}
    (ell : ℝ → ℝ) (T : ℕ)
    (hl : 0 < l) (hh : h < 1) (heta : 0 < eta)
    (hgamma : 0 ≤ gamma) (hwL : 0 ≤ wL) (hwR : 0 ≤ wR) (hz0 : 0 ≤ z0)
    (hv : ∀ q ∈ Set.Icc l h, q * (1 - q) ≤ v)
    (hbudget : 0 ≤ 2 * gamma * ((T : ℝ) - m0) + gamma - beta -
      eta * v - z0 * (1 - l) ^ T)
    (hseed : ∀ q ∈ Set.Icc l h, ∀ M : ℕ, M ≤ T → ∀ j : ℤ,
      0 ≤ lowMeanH q wL wR xi eta M j - lowMeanPsi alpha beta gamma m0 M +
        z0 * (1 - q) ^ M)
    (hmargin : ∀ q ∈ Set.Icc l h, ∀ mu ∈ Set.Icc (max muA (4 / q)) muB,
      0 < lowMeanPsi alpha beta gamma m0 mu - gamma * D * mu -
        eta * theta * q * (1 - q) * mu - z0 * Real.exp (-ell q * mu))
    {q mu : ℝ} (hq : q ∈ Set.Icc l h) (hmu : mu ∈ Set.Icc (max muA (4 / q)) muB)
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta q k M Y) = 0)
    (hvar : X.varM ≤ D * mu)
    (hdelta2 : X.expect (fun M Y => delta q k M Y ^ 2) ≤
      theta * (q * (1 - q)) * mu)
    (htail : X.expect (fun M _ => (1 - q) ^ M) ≤ Real.exp (-ell q * mu)) :
    ¬ X.WeakValley q k := by
  exact lowMean_noValley X k T (lt_of_lt_of_le hl hq.1) (lt_of_le_of_lt hq.2 hh)
    hq.1 heta hgamma hwL hwR hz0 (hv q hq) hbudget (hseed q hq)
    (hmargin q hq mu hmu) hX hmean hdelta hvar hdelta2 htail

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMeanPsi_recenter
#print axioms Erdos993Lean.Analytic.V213.lowMean_noValley
#print axioms Erdos993Lean.Analytic.V213.lowMean_noValley_on_domain
