module

public import Erdos993Lean.Analytic.V213.FinalInputBindings
public import Erdos993Lean.Analytic.V213.FiberAboveStartingMean

/-! Theorem 2.7 in the numerical interface consumed by Theorem 2.8. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem theorem27_input :
  ∀ (i : ℕ), i < 55 → ∀ {σ : Type} (X : Mixture σ) (j : ℤ) {lam mu : ℝ},
    lam ∈ Set.Icc (N44.Data.pieceLo.getD i 0 : ℝ) (N44.Data.pieceHi.getD i 0 : ℝ) →
    lowMeanFractionReal (lowMeanInputRowAt i).mu0 ≤ mu →
    X.IsProb → X.meanM = mu →
    X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y) = 0 →
    X.varM ≤ lowMeanFractionReal (lowMeanInputRowAt i).D * mu →
    X.expect (fun M Y => delta (FreeCountVariance.q lam) j M Y ^ 2) ≤
      lowMeanFractionReal (lowMeanInputRowAt i).theta *
        (FreeCountVariance.q lam * (1 - FreeCountVariance.q lam)) * mu →
    X.expect (fun M _ => (1 - FreeCountVariance.q lam) ^ M) ≤
      Real.exp (-((N44.Data.rates44.getD i []).getD 0 0 : ℝ) * mu) →
    ¬ X.WeakValley (FreeCountVariance.q lam) j := by
  intro i hi σ X j lam mu hlam hmu hX hmean hdelta hvar hdelta2 htail
  let id := fiberInputIdentityAt i
  have hidx : fiberInputIndex id = i := fiber_input_index_at i hi
  have hiota : (fiberInputRouteById id).iota = i := fiber_input_iota_at i hi
  have hlo : lowMeanFractionReal (fiberInputLoFraction id) ≤ lam := by
    simpa only [fiberInputLoFraction, hiota, lowMean_n44Lo_real] using hlam.1
  have hhi : lam ≤ lowMeanFractionReal (fiberInputHiFraction id) := by
    simpa only [fiberInputHiFraction, hiota, lowMean_n44Hi_real] using hlam.2
  have hmu' : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu := by
    rw [← fiber_input_starting_mean_eq]
    simpa only [fiberInputPaperRow, hidx] using hmu
  have hm : 0 ≤ mu := (fiber_input_starting_mean_positive id).le.trans hmu'
  apply fiber_noValley_above_starting_mean X id j hlo hhi hmu' hX hmean hdelta
  · simpa only [fiberInputPaperRow, hidx] using hvar
  · simpa only [fiberInputPaperRow, hidx] using hdelta2
  · apply htail.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (fiber_input_rate_le i hi)) hm

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.theorem27_input
