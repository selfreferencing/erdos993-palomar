module

public import Erdos993Lean.Analytic.V213.FiberAnalyticInputDomain
public import Erdos993Lean.Analytic.V213.FiberInputTarget
public import Erdos993Lean.Analytic.V213.FiberWeightPrices
public import Erdos993Lean.Analytic.V213.FiberSpikePrice

/-!
Actual original-input Eq96/99 price consumer on all41 analytic
routes. The actual target line and original q are retained. Exact
closed skew/mean/width guards, the positive actual rate and Eq97 feed
the checked all-eight-weight profile prices. No numerical or routing
premise substitutes for a printed theorem.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_analytic_input_deficit (id : FiberAnalyticInputIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberAnalyticInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id)))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).mu0 ≤ mu)
    (hM : 8 ≤ M) (ht : 1/3 ≤ (M : ℝ)/mu)
    (hcap : (M : ℝ)/mu ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) :
    fiberDeficit (FreeCountVariance.q lambda) mu (fiberInputTarget (fiberAnalyticInput id)) M ≤
      max 0 (max
        (fiberNamedProfile (fiberWeightById (fiberAnalyticWeight id)).profile ((M : ℝ)/mu)
          |fiberSkew (FreeCountVariance.q lambda)| (fiberRayAroot ((M : ℝ)/mu)))
        (fiberProfileE ((M : ℝ)/mu) |fiberSkew (FreeCountVariance.q lambda)| (fiberRayAroot ((M : ℝ)/mu)))) := by
  let pid := (fiberWeightById (fiberAnalyticWeight id)).profile
  let p := fiberRationalProfileById pid
  have hq := fiber_input_probability_domain (fiberAnalyticInput id) hl hh
  have hskew := fiber_analytic_input_profile_skew id hl hh
  have hm := fiber_analytic_input_profile_mean id hmu
  have hp := fiber_profile_parameters pid
  rcases hp with ⟨hm19,hs,hra,hrah,hr,hk,hcf0,hcf,hcd,hd,hloss,hR,hRh,hfloor,htcap⟩
  have hwidth := fiber_profile_actual_record_width pid hm hM ht
  have htarget := fiber_analytic_input_target id hcap
  have hdef := fiber_profile_deficit_bound (fiberRationalProfileRay pid) hwidth hq.1 hq.2
    hm19 hm hs hra hskew.1 hskew.2 ht (hcap.trans htcap) htarget.1 htarget.2
  simpa only [fiberNamedProfile] using hdef

theorem fiber_spike_term_activity {lambda mu ell : ℝ} (hlambda : 0 ≤ lambda)
    (hmu : 0 < mu) (g : ℝ → ℝ) (M : ℕ) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu ell g M =
      Real.exp (-mu*(ell-Real.log (1+lambda)*((M : ℝ)/mu))) *
        fiberDeficit (FreeCountVariance.q lambda) mu g M := by
  have hp : 0 < 1+lambda := by linarith only [hlambda]
  have hw : (1-FreeCountVariance.q lambda)⁻¹ = 1+lambda := by
    unfold FreeCountVariance.q
    field_simp [hp.ne']
    ring
  have he : Real.exp ((M : ℝ)*Real.log (1+lambda)) = (1+lambda)^M := by
    rw [Real.exp_nat_mul,Real.exp_log hp]
  have hid : (M : ℝ)*Real.log (1+lambda) + -ell*mu =
      -mu*(ell-Real.log (1+lambda)*((M : ℝ)/mu)) := by
    field_simp [hmu.ne'] <;> ring
  unfold fiberSpikeTerm
  rw [← inv_pow,hw,← he,← Real.exp_add,hid]

theorem fiber_analytic_input_price (id : FiberAnalyticInputIdentity) {lambda mu : ℝ} {M : ℕ}
    (hl : lowMeanFractionReal (fiberInputLoFraction (fiberAnalyticInput id)) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id)))
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).mu0 ≤ mu)
    (hM : 8 ≤ M) (ht : 1/3 ≤ (M : ℝ)/mu)
    (hts : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ts)
    (hcap : (M : ℝ)/mu ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu
      (lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0)
      (fiberInputTarget (fiberAnalyticInput id)) M <
        lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).eta_w := by
  have hlam := fiber_input_activity_nonneg (fiberAnalyticInput id) hl
  have hmu0 := (fiber_input_starting_mean_positive (fiberAnalyticInput id)).trans_le hmu
  have ht0 : 0 ≤ (M : ℝ)/mu := by positivity
  have hguardtime := fiber_input_analytic_guard_time id ht hts hcap
  have hguard := fiber_input_guard_actual_log id hlam hh hguardtime.1 hguardtime.2
  have hrate := fiber_input_actual_rate_positive id hlam hh ht0 hts hcap
  have hmean := fiber_input_weight_mean id hmu
  have hwm0 : 0 ≤ lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).mu_w := by
    cases hwi : fiberAnalyticWeight id <;> norm_num [fiberWeightById,lowMeanFractionReal]
  have hwg : lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).ell_w -
      lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).L_w*((M : ℝ)/mu) ≤
      lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
        Real.log (1+lambda)*((M : ℝ)/mu) := by linarith only [hguard]
  have hprod1 := mul_le_mul_of_nonneg_left hwg hwm0
  have hprod2 := mul_le_mul_of_nonneg_right hmean hrate.le
  have hexp : Real.exp (-mu*(lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
      Real.log (1+lambda)*((M : ℝ)/mu))) ≤
        Real.exp (-fiberWeightExponent (fiberAnalyticWeight id) ((M : ℝ)/mu)) := by
    apply Real.exp_le_exp.mpr
    unfold fiberWeightExponent
    linarith only [hprod1,hprod2]
  have hdef := fiber_analytic_input_deficit id hl hh hmu hM ht hcap
  have hmul := mul_le_mul hexp hdef
    (fiber_deficit_nonneg (FreeCountVariance.q lambda) mu (fiberInputTarget (fiberAnalyticInput id)) M)
    (Real.exp_pos _).le
  have hskew := fiber_analytic_input_profile_skew id hl hh
  have hprice := fiber_weight_price (fiberAnalyticWeight id) ht hcap
    (abs_nonneg (fiberSkew (FreeCountVariance.q lambda))) hskew.2
  rw [fiber_spike_term_activity hlam hmu0]
  exact hmul.trans_lt hprice

end Erdos993Lean.Analytic.V213
