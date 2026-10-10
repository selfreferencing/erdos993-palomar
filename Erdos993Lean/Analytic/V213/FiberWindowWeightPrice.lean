module

public import Erdos993Lean.Analytic.V213.FiberCornerBounds
public import Erdos993Lean.Analytic.V213.FiberWindowNamedDeficit
public import Erdos993Lean.Analytic.V213.FiberAnalyticInputPrice

/-!
Exact F13 weighted-window consumers. The actual unweighted deficit
and canonical logarithm gap imply a strict price on all eight nontrivial
windows. The original activity and original q are retained throughout.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_window_weight_price_guards (id : FiberWindowWeightIdentity) :
    let r := fiberWindowWeightById id
    let w := fiberWindowById r.window
    let c := fiberWindowCornerById r.corner
    0 < lowMeanFractionReal w.L_W ∧ 0 < lowMeanFractionReal c.Z_W ∧
      0 ≤ lowMeanFractionReal c.mu_c ∧ 0 ≤ lowMeanFractionReal c.L_c ∧
      0 < lowMeanFractionReal c.ell_c - lowMeanFractionReal c.L_c * lowMeanFractionReal w.h := by
  cases id <;> norm_num [fiberWindowWeightById,fiberWindowCornerById,fiberWindowById,lowMeanFractionReal]

theorem fiber_discount_log_lt {x z a : ℝ} (hx : 0 < x) (hz : 0 < z)
    (h : Real.log (x/z) < a) : Real.exp (-a)*x < z := by
  have he := Real.exp_lt_exp.mpr h
  rw [Real.exp_log (div_pos hx hz)] at he
  have hm := mul_lt_mul_of_pos_left he (Real.exp_pos (-a))
  rw [← Real.exp_add,neg_add_cancel,Real.exp_zero] at hm
  have hm' : Real.exp (-a)*x/z < 1 := by simpa only [mul_div_assoc] using hm
  simpa only [one_mul] using (div_lt_iff₀ hz).mp hm'

theorem fiber_window_weight_exponential (id : FiberWindowWeightIdentity) :
    let r := fiberWindowWeightById id
    let w := fiberWindowById r.window
    let c := fiberWindowCornerById r.corner
    Real.exp (-lowMeanFractionReal c.mu_c *
      (lowMeanFractionReal c.ell_c-lowMeanFractionReal c.L_c*lowMeanFractionReal w.h)) *
        lowMeanFractionReal w.L_W < lowMeanFractionReal c.Z_W := by
  have hg := fiber_window_weight_price_guards id
  have h := fiber_window_weight_strict_gap id
  convert fiber_discount_log_lt hg.1 hg.2.1 h using 1 <;> ring

theorem fiber_window_weighted_price (id : FiberWindowWeightIdentity) {lambda mu ell : ℝ} {M : ℕ}
    (hlambda : 0 ≤ lambda) (hmu : 0 < mu)
    (hql : 1/4 ≤ FreeCountVariance.q lambda) (hqh : FreeCountVariance.q lambda ≤ 3/4)
    (har : lowMeanFractionReal
      (fiberOuterClassById (fiberWindowById (fiberWindowWeightById id).window).outerClass).skew_lower ≤
        |fiberSkew (FreeCountVariance.q lambda)|)
    (hrb : |fiberSkew (FreeCountVariance.q lambda)| ≤ lowMeanFractionReal
      (fiberOuterClassById (fiberWindowById (fiberWindowWeightById id).window).outerClass).skew_upper)
    (hmean : lowMeanFractionReal
      (fiberOuterClassById (fiberWindowById (fiberWindowWeightById id).window).outerClass).mu_D ≤ mu)
    (htl : lowMeanFractionReal (fiberWindowById (fiberWindowWeightById id).window).l ≤ (M : ℝ)/mu)
    (hth : (M : ℝ)/mu ≤ lowMeanFractionReal (fiberWindowById (fiberWindowWeightById id).window).h)
    (hcornerMean : lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById id).corner).mu_c ≤ mu)
    (hell : lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById id).corner).ell_c ≤ ell)
    (hlog : Real.log (1+lambda) ≤ lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById id).corner).L_c) :
    fiberSpikeTerm (FreeCountVariance.q lambda) mu ell
      (fiberWindowTarget (fiberWindowWeightById id).window) M <
        lowMeanFractionReal (fiberWindowCornerById (fiberWindowWeightById id).corner).Z_W := by
  let r := fiberWindowWeightById id
  let w := fiberWindowById r.window
  let c := fiberWindowCornerById r.corner
  have hg := fiber_window_weight_price_guards id
  have ht0 : 0 ≤ (M : ℝ)/mu := div_nonneg (Nat.cast_nonneg _) hmu.le
  have hlogmul := mul_le_mul_of_nonneg_right hlog ht0
  have htimemul := mul_le_mul_of_nonneg_left hth hg.2.2.2.1
  have hrate : lowMeanFractionReal c.ell_c-lowMeanFractionReal c.L_c*lowMeanFractionReal w.h ≤
      ell-Real.log (1+lambda)*((M : ℝ)/mu) := by
    linarith only [hell,hlogmul,htimemul]
  have hactualpos := hg.2.2.2.2.trans_le hrate
  have hprod1 := mul_le_mul_of_nonneg_left hrate hg.2.2.1
  have hprod2 := mul_le_mul_of_nonneg_right hcornerMean hactualpos.le
  have hexp : Real.exp (-mu*(ell-Real.log (1+lambda)*((M : ℝ)/mu))) ≤
      Real.exp (-lowMeanFractionReal c.mu_c*(lowMeanFractionReal c.ell_c-lowMeanFractionReal c.L_c*lowMeanFractionReal w.h)) := by
    apply Real.exp_le_exp.mpr
    linarith only [hprod1,hprod2]
  have hd := fiber_window_named_deficit r.window hql hqh har hrb hmean htl hth
  rw [fiber_spike_term_activity hlambda hmu]
  have hbound := mul_le_mul hexp hd (fiber_deficit_nonneg _ _ _ _) (Real.exp_pos _).le
  exact hbound.trans_lt (fiber_window_weight_exponential id)

end Erdos993Lean.Analytic.V213
