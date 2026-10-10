module

public import Erdos993Lean.Analytic.V213.FiberAveragingMargin
public import Erdos993Lean.Analytic.V213.FiberInputHighComparison
public import Erdos993Lean.Analytic.V213.FiberSpikeAveraging

/-!
Literal Theorem2.7, no valley above the actual starting means.
For every one of55 actual closed input intervals, all
real means above mu0 and every integer rank, the actual high-width
comparison and strict Eq88 margin are discharged. Probability and the
five printed Eq10 moment hypotheses are retained exactly. This is the
generic mixture theorem; forest specialization belongs to later assembly.
Original q remains in the actual Laplace moment, including below1/2.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_input_averaging_parameters (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputQloFraction id) ∈ Set.Icc (1/4 : ℝ) (3/4) ∧
    lowMeanFractionReal (fiberInputQhiFraction id) ∈ Set.Icc (1/4 : ℝ) (3/4) ∧
    0 < lowMeanFractionReal (fiberInputRouteById id).ts ∧
    lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind) ∈ Set.Icc (0 : ℝ) (2/5) ∧
    0 ≤ lowMeanFractionReal (fiberInputClassBeta (fiberInputRouteById id).kind) := by
  have hd := fiber_input_domain_facts id
  have hs := (lowMean_fraction_le_iff hd.1 hd.2.1).mp hd.2.2.2.2.2.2.1
  have hlo := fiber_input_probability_domain id (le_refl _) hs
  have hhi := fiber_input_probability_domain id hs (le_refl _)
  rw [←fiber_input_qlo_real] at hlo
  rw [←fiber_input_qhi_real] at hhi
  have ht : 0 < lowMeanFractionReal (fiberInputRouteById id).ts := by
    cases id <;> norm_num [fiberInputRouteById,lowMeanFractionReal]
  have hb0 : 0 ≤ lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind) := by
    cases id <;> norm_num [fiberInputClassB,fiberInputOuterClass,fiberOuterClassById,
      fiberInputRouteById,lowMeanFractionReal]
  have hb := fiber_tail_input_target_bounds id
  exact ⟨hlo,hhi,ht,⟨hb0,hb.1⟩,hb.2⟩

theorem fiber_noValley_above_starting_mean {ι : Type} (X : Mixture ι)
    (id : FiberInputIdentity) (k : ℤ) {lambda mu : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu)
    (hX : X.IsProb) (hmean : X.meanM = mu)
    (hdelta : X.expect (fun M Y => delta (FreeCountVariance.q lambda) k M Y) = 0)
    (hvar : X.varM ≤ lowMeanFractionReal (fiberInputPaperRow id).D * mu)
    (hdelta2 : X.expect (fun M Y => delta (FreeCountVariance.q lambda) k M Y ^ 2) ≤
      lowMeanFractionReal (fiberInputPaperRow id).theta *
        (FreeCountVariance.q lambda * (1-FreeCountVariance.q lambda)) * mu)
    (htail : X.expect (fun M _ => (1-FreeCountVariance.q lambda)^M) ≤
      Real.exp (-lowMeanFractionReal (fiberInputRouteById id).ell0 * mu)) :
    ¬ X.WeakValley (FreeCountVariance.q lambda) k := by
  rcases fiber_input_averaging_parameters id with ⟨hlo,hhi,hts,hb,hbeta⟩
  have hmup := (fiber_input_starting_mean_positive id).trans_le hmu
  apply fiber_spike_averaging X k hlo hhi (fiber_input_q_interval id hl hh) hmup hts hb hbeta
    ?_ ?_ hX hmean hdelta hvar hdelta2 htail
  · intro M j hM
    have ht := (le_div_iff₀ hmup).2 hM
    simpa only [fiberInputTarget,fiberTargetLine] using fiber_input_high_comparison id hl hh hmu M j ht
  · have hm := (fiber_averaging_inequalities id hl hh hmu).2.2
    change 0 < fiberInputAveragingMargin id lambda mu
    exact (by norm_num : (0 : ℝ) < 1/500).trans hm

end Erdos993Lean.Analytic.V213
