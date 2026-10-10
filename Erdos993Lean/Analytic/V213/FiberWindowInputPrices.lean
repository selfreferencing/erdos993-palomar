module

public import Erdos993Lean.Analytic.V213.FiberWindowInputCorners
public import Erdos993Lean.Analytic.V213.FiberWindowWeightPrice
public import Erdos993Lean.Analytic.V213.FiberCoupledInputRates

/-!
Actual original-q weighted-window prices on every served input.
Whole closed Params intervals and actual starting means are retained.
The first six routes use the coupled C1/C2 rate, with non-strict prices
0 and .11755. Each other window has the printed strict class price.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberCornerRateWindowInput : FiberCornerRateIdentity → FiberWindowInputIdentity
  | .iota0 => .iota0 | .iota1 => .iota1 | .iota2 => .iota2
  | .iota3 => .iota3 | .iota4 => .iota4 | .iota5 => .iota5

def fiberCornerRateWindow : FiberCornerRateIdentity → FiberWindowIdentity
  | .iota0 | .iota1 | .iota2 => .window1
  | .iota3 | .iota4 | .iota5 => .window2

theorem fiber_window_input_deficit (id : FiberWindowInputIdentity) (wid : FiberWindowIdentity)
    (hw : wid ∈ fiberWindowInputWindows id) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberWindowInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberWindowInput id)))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).mu0 ≤ mu)
    (htl : lowMeanFractionReal (fiberWindowById wid).l ≤ (M : ℝ)/mu)
    (hth : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberWindowById wid).h) :
    fiberDeficit (FreeCountVariance.q lambda) mu (fiberInputTarget (fiberWindowInput id)) M ≤
      lowMeanFractionReal (fiberWindowById wid).L_W := by
  have hq := fiber_input_probability_domain (fiberWindowInput id) hl hh
  have hs := fiber_window_input_skew id hl hh
  have hm := fiber_window_input_mean id hmu
  have hclass := fiber_window_input_class id wid hw
  rw [← hclass] at hs hm
  have h := fiber_window_named_deficit wid hq.1 hq.2 hs.1 hs.2 hm htl hth
  rw [fiber_window_input_target id wid hw] at h
  exact h

theorem fiber_window_input_weighted_price (id : FiberWindowInputIdentity) (wid : FiberWindowWeightIdentity)
    (hw : (fiberWindowWeightById wid).window ∈ fiberWindowInputWindows id)
    (hc : fiberWindowInputCorner id = some (fiberWindowWeightById wid).corner)
    {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberWindowInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberWindowInput id)))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).mu0 ≤ mu)
    (htl : lowMeanFractionReal (fiberWindowById (fiberWindowWeightById wid).window).l ≤ (M : ℝ)/mu)
    (hth : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberWindowById (fiberWindowWeightById wid).window).h) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById (fiberWindowInput id)).ell0)
      (fiberInputTarget (fiberWindowInput id)) M <
        lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById wid).corner).Z_W := by
  have hlam := fiber_input_activity_nonneg (fiberWindowInput id) hl
  have hmup := (fiber_input_starting_mean_positive (fiberWindowInput id)).trans_le hmu
  have hq := fiber_input_probability_domain (fiberWindowInput id) hl hh
  have hs := fiber_window_input_skew id hl hh
  have hm := fiber_window_input_mean id hmu
  have hclass := fiber_window_input_class id (fiberWindowWeightById wid).window hw
  rw [← hclass] at hs hm
  have hcorn := fiber_window_input_corner id _ hc hlam hh hmu
  have h := fiber_window_weighted_price wid hlam hmup hq.1 hq.2 hs.1 hs.2 hm htl hth hcorn.1 hcorn.2.1 hcorn.2.2
  rw [fiber_window_input_target id _ hw] at h
  exact h

theorem fiber_window_coupled_input_price (id : FiberCornerRateIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberCornerRateById id).input) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberCornerRateById id).input))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).mu0 ≤ mu)
    (htl : lowMeanFractionReal (fiberWindowById (fiberCornerRateWindow id)).l ≤ (M : ℝ)/mu)
    (hth : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberWindowById (fiberCornerRateWindow id)).h) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ell0)
      (fiberInputTarget (fiberCornerRateById id).input) M ≤
        lowMeanFractionReal (fiberWindowById (fiberCornerRateWindow id)).L_W := by
  have hi : fiberWindowInput (fiberCornerRateWindowInput id) = (fiberCornerRateById id).input := by cases id <;> rfl
  have hw : fiberCornerRateWindow id ∈ fiberWindowInputWindows (fiberCornerRateWindowInput id) := by
    cases id <;> simp [fiberCornerRateWindow,fiberCornerRateWindowInput,fiberWindowInputWindows]
  have hlam := fiber_input_activity_nonneg (fiberCornerRateById id).input hl
  have hmup := (fiber_input_starting_mean_positive (fiberCornerRateById id).input).trans_le hmu
  have ht0 : 0 ≤ (M : ℝ)/mu := div_nonneg (Nat.cast_nonneg _) hmup.le
  have hts : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ts := by
    cases id <;> simpa only [fiberCornerRateWindow,fiberCornerRateById,fiberInputRouteById,fiberWindowById] using hth
  have hp := fiber_coupled_input_rate_positive id hlam hh ht0 hts
  have he : Real.exp (-mu*(lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ell0-
      Real.log (1+lambda)*((M : ℝ)/mu))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hmup.le) hp.le)
  have hd := fiber_window_input_deficit (fiberCornerRateWindowInput id) (fiberCornerRateWindow id) hw
    (lambda := lambda) (mu := mu) (M := M)
  rw [hi] at hd
  have hd' := hd hl hh hmu htl hth
  rw [fiber_spike_term_activity hlam hmup]
  simpa only [one_mul] using mul_le_mul he hd' (fiber_deficit_nonneg _ _ _ _) (by norm_num : (0 : ℝ) ≤ 1)

end Erdos993Lean.Analytic.V213
