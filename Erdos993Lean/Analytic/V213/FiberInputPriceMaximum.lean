module

public import Erdos993Lean.Analytic.V213.FiberPriceCheck
public import Erdos993Lean.Analytic.V213.FiberInputRemainderCover
public import Erdos993Lean.Analytic.V213.FiberTailInputLarge

/-!
The actual original-q spike price is bounded by the printed F16 maximum
on every one of the55 input intervals, for all means above the actual
starting mean. Natural widths0--7, the strict large-tail cut, all profile
ranges and all closed windows cover the entire strict spike domain.
The finite supremum is attained, so no pointwise-to-strict-sup inference
is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_input_spike_term_le_maximum (id : FiberInputIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu)
    (hcut : (M : ℝ) < lowMeanFractionReal (fiberInputRouteById id).ts*mu) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById id).ell0) (fiberInputTarget id) M ≤
      lowMeanFractionReal (fiberInputPriceFraction id) := by
  have hmup := (fiber_input_starting_mean_positive id).trans_le hmu
  have hts : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberInputRouteById id).ts :=
    ((div_lt_iff₀ hmup).mpr hcut).le
  by_cases hsmall : M ≤ 7
  · exact (fiber_tail_input_small_price id hl hh hmu hsmall).le.trans (fiber_price_small_tail_le id)
  have hM : 8 ≤ M := by omega
  by_cases hlarge : (M : ℝ)/mu < lowMeanFractionReal (fiberInputRouteById id).c
  · exact (fiber_tail_input_large_price id hl hh hmu hM ((div_lt_iff₀ hmup).mp hlarge)).le.trans
      (fiber_price_large_tail_le id)
  rcases fiber_input_remainder_cover id (le_of_not_gt hlarge) hts with hprofile | hwindow | hweighted
  · rcases hprofile with ⟨aid,hi,ht,hcap⟩
    subst id
    exact (fiber_analytic_input_price aid hl hh hmu hM ht hts hcap).le.trans (fiber_price_analytic_le aid)
  · rcases hwindow with ⟨rid,hi,htl,hth⟩
    subst id
    have hp := fiber_window_coupled_input_price rid hl hh hmu htl hth
    have hmem : fiberCornerRateWindow rid ∈ fiberWindowInputWindows (fiberCornerRateWindowInput rid) := by
      cases rid <;> simp [fiberCornerRateWindow,fiberCornerRateWindowInput,fiberWindowInputWindows]
    have hb := fiber_price_window_le (fiberCornerRateWindowInput rid) (fiberCornerRateWindow rid) hmem
    have he : fiberWindowInput (fiberCornerRateWindowInput rid) = (fiberCornerRateById rid).input := by
      cases rid <;> rfl
    have hprice : fiberWindowPriceFraction (fiberCornerRateWindow rid) =
        (fiberWindowById (fiberCornerRateWindow rid)).L_W := by cases rid <;> rfl
    rw [he,hprice] at hb
    exact hp.trans hb
  · rcases hweighted with ⟨iid,wid,hi,hw,hc,htl,hth⟩
    subst id
    have hp := fiber_window_input_weighted_price iid wid hw hc hl hh hmu htl hth
    have hb := fiber_price_window_le iid (fiberWindowWeightById wid).window hw
    have he : fiberWindowPriceFraction (fiberWindowWeightById wid).window =
        (fiberWindowCornerById (fiberWindowWeightById wid).corner).Z_W := by cases wid <;> rfl
    rw [he] at hb
    exact hp.le.trans hb

theorem fiber_input_spike_price_le_maximum (id : FiberInputIdentity) {lambda mu : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id))
    (hmu : lowMeanFractionReal (fiberInputRouteById id).mu0 ≤ mu) :
    fiberSpikePrice (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById id).ell0)
      (lowMeanFractionReal (fiberInputRouteById id).ts) (fiberInputTarget id) ≤
      lowMeanFractionReal (fiberInputPriceFraction id) := by
  have hts : 0 < lowMeanFractionReal (fiberInputRouteById id).ts := by
    cases id <;> norm_num [fiberInputRouteById,lowMeanFractionReal]
  have hmup := (fiber_input_starting_mean_positive id).trans_le hmu
  obtain ⟨M,hM,he,_⟩ := fiber_spike_price_attained (FreeCountVariance.q lambda)
    (lowMeanFractionReal (fiberInputRouteById id).ell0) (fiberInputTarget id) hts hmup
  rw [he]
  exact fiber_input_spike_term_le_maximum id hl hh hmu hM

end Erdos993Lean.Analytic.V213
