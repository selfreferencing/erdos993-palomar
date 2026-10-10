module

public import Erdos993Lean.Analytic.V213.FiberAveragingBudget
public import Erdos993Lean.Analytic.V213.FiberInputPriceMaximum

/-!
Literal Theorem6.23: for all55 closed original activity intervals and
every real mean above the actual starting mean, the actual Eq88 left
side is at least its defined per-input epsilon and strictly >1/500.
The actual original q remains in the spike inverse Laplace weight.
No Section5 replacement premise.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberInputAveragingMargin (id : FiberInputIdentity) (lambda mu : ℝ) : ℝ :=
  let p := fiberInputPaperRow id
  let rhi := fiberInputSkewHigh (lowMeanFractionReal (fiberInputQloFraction id))
    (lowMeanFractionReal (fiberInputQhiFraction id))
  1+lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind)-lowMeanFractionReal p.theta-
    9*lowMeanFractionReal p.D/(2*mu)-rhi^2/((1-rhi^2)*mu)-
    fiberSpikePrice (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById id).ell0)
      (lowMeanFractionReal (fiberInputRouteById id).ts) (fiberInputTarget id)

theorem fiber_averaging_margin_lower (id : FiberInputIdentity) {lambda mu : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) :
    fiberInputEpsilon id ≤ fiberInputAveragingMargin id lambda mu := by
  rcases fiber_budget_input_parameters id with ⟨_,_,_,_,_,hr,_,hRh,hD0,_⟩
  have hr0 := fiber_skew_high_nonneg (lowMeanFractionReal (fiberInputQloFraction id))
    (lowMeanFractionReal (fiberInputQhiFraction id))
  have hcost := fiber_averaging_cost_mean_mono hD0 hr0 (hr.trans hRh)
    (fiber_input_starting_mean_positive id) hmu
  have hp := fiber_input_spike_price_le_maximum id hl hh hmu
  unfold fiberInputEpsilon fiberInputAveragingMargin
  dsimp only
  linarith only [hcost.1,hcost.2,hp]

theorem fiber_averaging_inequalities (id : FiberInputIdentity) {lambda mu : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) :
    fiberInputEpsilon id ≤ fiberInputAveragingMargin id lambda mu ∧
    (1/500 : ℝ) < fiberInputEpsilon id ∧
    (1/500 : ℝ) < fiberInputAveragingMargin id lambda mu := by
  have he := fiber_input_epsilon_strict id
  have hm := fiber_averaging_margin_lower id hl hh hmu
  exact ⟨hm,he,he.trans_le hm⟩

end Erdos993Lean.Analytic.V213
