module

public import Erdos993Lean.Analytic.V213.FiberInputRateCheck

/-!
Literal Eq97 over every closed guard interval and actual activity
interval. Strict positive actual rate is proved separately before any
mean transfer; a printed weight's affine rate may itself be negative.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

/-- An affine lower bound at both endpoints holds on the full interval. -/
theorem fiber_affine_closed_lower {a b l h t k : ℝ}
    (hl : k ≤ a+b*l) (hh : k ≤ a+b*h) (htl : l ≤ t) (hth : t ≤ h) :
    k ≤ a+b*t := by
  by_cases hb : 0 ≤ b
  · exact hl.trans (add_le_add (le_refl a) (mul_le_mul_of_nonneg_left htl hb))
  · exact hh.trans (add_le_add (le_refl a) (mul_le_mul_of_nonpos_left hth (le_of_not_ge hb)))

theorem fiber_analytic_end_real (id : FiberAnalyticInputIdentity) :
    lowMeanFractionReal (fiberAnalyticEndFraction id) =
      min (lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ts)
        (fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) := by
  have hf := fiber_input_rate_facts id
  have hts := hf.1.2.2.2.2.2.2.2.2.2.1
  have hc := fiber_profile_time_cap_fraction (fiberWeightById (fiberAnalyticWeight id)).profile
  dsimp [fiberAnalyticEndFraction]
  split_ifs with h
  · have hr := (lowMean_fraction_le_iff hts hc.1).mp h
    rw [hc.2] at hr
    exact (min_eq_left hr).symm
  · have hr : ¬ lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ts ≤
        lowMeanFractionReal (fiberProfileTimeCapFraction (fiberWeightById (fiberAnalyticWeight id)).profile) :=
      fun hh => h ((lowMean_fraction_le_iff hts hc.1).mpr hh)
    rw [hc.2] at hr ⊢
    exact (min_eq_right (le_of_not_ge hr)).symm

theorem fiber_input_guard_interval (id : FiberAnalyticInputIdentity) {t : ℝ}
    (htl : lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_lo ≤ t)
    (hth : t ≤ lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_hi) :
    (1 / 100000 : ℝ) ≤ lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 -
      lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).ell_w +
      (lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).L_w -
        lowMeanFractionReal (fiberInputLogById id).upper) * t :=
  fiber_affine_closed_lower (fiber_input_guard_endpoints id).1
    (fiber_input_guard_endpoints id).2 htl hth

theorem fiber_input_guard_actual_log (id : FiberAnalyticInputIdentity) {lambda t : ℝ}
    (hlambda : 0 ≤ lambda)
    (hhi : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id)))
    (htl : lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_lo ≤ t)
    (hth : t ≤ lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_hi) :
    lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).ell_w -
      lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).L_w*t + 1/100000 ≤
    lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 - Real.log (1+lambda)*t := by
  have hf := fiber_input_rate_facts id
  have htl0 : 0 ≤ lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).guard_lo := by
    simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using
      (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid])
        hf.1.2.2.2.2.2.2.2.1).mp hf.2.1.2.2.2.2.2.2.2.2.2.1
  have ht0 := htl0.trans htl
  have hlog := (Real.log_le_log (by linarith only [hlambda] : 0 < 1+lambda)
    (by linarith only [hhi] : 1+lambda ≤ 1+lowMeanFractionReal
      (fiberInputHiFraction (fiberAnalyticInput id)))).trans (fiber_input_log_upper id)
  have hprod := mul_le_mul_of_nonneg_right hlog ht0
  have hguard := fiber_input_guard_interval id htl hth
  linarith only [hprod,hguard]

theorem fiber_input_actual_rate_positive (id : FiberAnalyticInputIdentity) {lambda t : ℝ}
    (hlambda : 0 ≤ lambda)
    (hhi : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberAnalyticInput id)))
    (ht : 0 ≤ t) (hts : t ≤ lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ts)
    (htp : t ≤ fiberProfileTimeCap (fiberWeightById (fiberAnalyticWeight id)).profile) :
    0 < lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).ell0 - Real.log (1+lambda)*t := by
  have hf := fiber_input_rate_facts id
  have hU : 0 ≤ lowMeanFractionReal (fiberInputLogById id).upper := by
    unfold lowMeanFractionReal
    exact div_nonneg (by exact_mod_cast hf.2.1.2.2.2.2.2.2.2.1) (Nat.cast_nonneg _)
  have hend : t ≤ lowMeanFractionReal (fiberAnalyticEndFraction id) := by
    rw [fiber_analytic_end_real]; exact le_min hts htp
  have hlog := (Real.log_le_log (by linarith only [hlambda] : 0 < 1+lambda)
    (by linarith only [hhi] : 1+lambda ≤ 1+lowMeanFractionReal
      (fiberInputHiFraction (fiberAnalyticInput id)))).trans (fiber_input_log_upper id)
  have hp1 := mul_le_mul_of_nonneg_right hlog ht
  have hp2 := mul_le_mul_of_nonneg_left hend hU
  have hpos := fiber_input_rate_endpoint_positive id
  linarith only [hp1,hp2,hpos]

theorem fiber_input_weight_mean (id : FiberAnalyticInputIdentity) {mu : ℝ}
    (hmu : lowMeanFractionReal (fiberInputRouteById (fiberAnalyticInput id)).mu0 ≤ mu) :
    lowMeanFractionReal (fiberWeightById (fiberAnalyticWeight id)).mu_w ≤ mu := by
  have hf := fiber_input_rate_facts id
  exact ((lowMean_fraction_le_iff hf.1.2.2.2.2.1 hf.1.2.2.2.1).mp
    hf.2.1.2.2.2.2.2.2.2.2.1).trans hmu

end Erdos993Lean.Analytic.V213
