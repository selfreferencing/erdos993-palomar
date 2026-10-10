module

public import Erdos993Lean.Analytic.V213.FiberTailInputRates

/-!
Actual original-q large-tail prices for all55 input intervals. Every
rate, skew, mean and cut guard is discharged from the accepted source
rows. The shifted large-tail mean remains max(least-mu,8/c).

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_input_large_price (id : FiberInputIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu)
    (hM : 8 ≤ M) (hcut : (M : ℝ) < lowMeanFractionReal (fiberInputRouteById id).c*mu) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById id).ell0) (fiberInputTarget id) M <
      lowMeanFractionReal (fiberTailById (fiberInputTail id)).Z_small := by
  have hlam := fiber_input_activity_nonneg id hl
  have hq := fiber_input_probability_domain id hl hh
  have hm := fiber_tail_input_mean id hmu
  have hcap := fiber_tail_cap_parameters (fiberInputTail id)
  have hskew := fiber_tail_input_skew id hl hh
  have htarget := fiber_tail_input_target_bounds id
  have hlog := fiber_input_original_log hlam
  have hcut' : (M : ℝ) < lowMeanFractionReal (fiberTailById (fiberInputTail id)).c*mu := by
    rw [fiber_tail_input_cut]
    exact hcut
  exact fiber_tail_large_transfer (fiberInputTail id) hq hm hM hcut'
    hcap.1 hcap.2.1 hskew hcap.2.2 htarget.1 htarget.2 hlog.le (le_refl _)
    (fiber_tail_input_large_rate id hl hh)

end Erdos993Lean.Analytic.V213
