module

public import Erdos993Lean.Analytic.V213.FinalAboveStartingMean
public import Erdos993Lean.Analytic.V213.LowMeanGroupSynthesis
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceRateFinite

/-! Printed Theorem 2.8 on every closed retained input interval.
Both mean regimes include their common endpoint. The high-mean input is
the merged Theorem 2.7, with its numeric interface discharged. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

/-- The free-count mean is nonnegative for a probability mixture. -/
theorem mixture_meanM_nonneg {σ : Type} (X : Mixture σ) (hX : X.IsProb) :
    0 ≤ X.meanM := by
  unfold Mixture.meanM Mixture.expect
  exact Finset.sum_nonneg (fun s hs => mul_nonneg (hX.1 s hs) (Nat.cast_nonneg _))

/-- Theorem 2.8, for each closed input containing the activity. -/
theorem theorem28 (i : ℕ) (hi : i < 55)
    {σ : Type} (X : Mixture σ) (j : ℤ) {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ) (N44.Data.pieceHi.getD i 0 : ℝ))
    (hmu : 4 / FreeCountVariance.q lam ≤ mu)
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y) = 0)
    (hvar : X.varM ≤ lowMeanFractionReal (lowMeanInputRowAt i).D * mu)
    (hdelta2 : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y ^ 2) ≤
      lowMeanFractionReal (lowMeanInputRowAt i).theta *
        (FreeCountVariance.q lam * (1 - FreeCountVariance.q lam)) * mu)
    (htail : X.expect (fun M _ => (1 - FreeCountVariance.q lam) ^ M) ≤
      Real.exp (-ZeroTiltLaplace.ellH lam * mu)) :
    ¬ X.WeakValley (FreeCountVariance.q lam) j := by
  by_cases hlow : mu ≤ lowMeanFractionReal (lowMeanInputRowAt i).mu0
  · exact lowMean_input_noValley i hi X j hlam ⟨hmu, hlow⟩ hX hmean hdelta hvar hdelta2 htail
  · have hm : 0 ≤ mu := by
      rw [← hmean]
      exact mixture_meanM_nonneg X hX
    have hr := ZeroTiltLaplace.PrintedRates.retained_input_rate_le hi hlam.1 hlam.2
    have he : Real.exp (-ZeroTiltLaplace.ellH lam * mu) ≤
        Real.exp (-((N44.Data.rates44.getD i []).getD 0 0 : ℝ) * mu) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hr) hm
    exact theorem27_input i hi X j hlam (le_of_not_ge hlow) hX hmean hdelta hvar hdelta2 (htail.trans he)

/-- The stronger Dhat variance cap narrows the same mixture class. -/
theorem theorem28_Dhat (i : ℕ) (hi : i < 55)
    {σ : Type} (X : Mixture σ) (j : ℤ) {lam mu : ℝ}
    (hlam : lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ) (N44.Data.pieceHi.getD i 0 : ℝ))
    (hmu : 4 / FreeCountVariance.q lam ≤ mu)
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y) = 0)
    (hvar : X.varM ≤ FreeCountVariance.Dhat lam * mu)
    (hdelta2 : X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y ^ 2) ≤
      lowMeanFractionReal (lowMeanInputRowAt i).theta *
        (FreeCountVariance.q lam * (1 - FreeCountVariance.q lam)) * mu)
    (htail : X.expect (fun M _ => (1 - FreeCountVariance.q lam) ^ M) ≤
      Real.exp (-ZeroTiltLaplace.ellH lam * mu)) :
    ¬ X.WeakValley (FreeCountVariance.q lam) j := by
  have hm : 0 ≤ mu := by
    rw [← hmean]
    exact mixture_meanM_nonneg X hX
  exact theorem28 i hi X j hlam hmu hX hmean hdelta
    (hvar.trans (mul_le_mul_of_nonneg_right (lowMean_input_Dhat_bound i hi hlam) hm)) hdelta2 htail

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.theorem28
#print axioms Erdos993Lean.Analytic.V213.theorem28_Dhat

#print axioms Erdos993Lean.Analytic.V213.mixture_meanM_nonneg
