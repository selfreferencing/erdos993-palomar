module

public import Erdos993Lean.Analytic.V213.FiberTailTransfers

/-!
Weighted small-tail and general large-tail transfers. The
small guard is evaluated at7 divided by the least table mean. The
large branch retains its different shifted m=max(mu0,8/c). These
explicit guards must be discharged on actual closed input intervals.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_weighted_small_transfer (id : FiberTailIdentity) (wid : FiberWeightIdentity)
    (hw : (fiberTailById id).weight = some wid) {q mu rhi b beta ell Lb : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4 : ℝ) (3/4))
    (hmu : lowMeanFractionReal (fiberTailById id).mu ≤ mu) (hM : M ≤ 7)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hC : fiberTailC rhi ≤ lowMeanFractionReal (fiberTailById id).C)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta) (hL : -Real.log (1-q) ≤ Lb)
    (hgeom : 1 ≤ (27/40 : ℝ)*Real.exp Lb)
    (hguard : fiberTailXA id ≤ ell*lowMeanFractionReal (fiberTailById id).mu-7*Lb) :
    fiberSpikeTerm q mu ell (fun t => b+beta*(t-1)) M <
      lowMeanFractionReal (fiberTailById id).Z_a := by
  have hp := fiber_tail_real_parameters id
  have hmup : 0 < lowMeanFractionReal (fiberTailById id).mu := by linarith only [hp.1]
  have hLb0 : 0 ≤ Lb := by
    have hlog := Real.log_nonpos (by linarith [hq.2] : 0 ≤ 1-q) (by linarith [hq.1] : 1-q ≤ 1)
    linarith only [hlog,hL]
  have hX : 3/2 ≤ fiberTailXA id := by
    cases id <;> norm_num [fiberTailXA,fiberTailById,fiberWeightById,lowMeanFractionReal]
  have hdecay : 3/2 ≤ ell*lowMeanFractionReal (fiberTailById id).mu := by
    linarith only [hguard,hX,hLb0]
  have h := fiber_tail_small_price hq hp.1 hmu hM hr0 hr1 hr hb hbeta hL hdecay
  rw [max_eq_right (one_le_pow₀ hgeom)] at h
  have heq : (51*fiberTailC rhi/200)*(lowMeanFractionReal (fiberTailById id).mu)^(3/2 : ℝ)*
      Real.exp (-ell*lowMeanFractionReal (fiberTailById id).mu)*(((27/40 : ℝ)*Real.exp Lb)^7) =
      ((51/200 : ℝ)*fiberTailC rhi*(27/40 : ℝ)^7)*
      (lowMeanFractionReal (fiberTailById id).mu)^(3/2 : ℝ)*
      Real.exp (-ell*lowMeanFractionReal (fiberTailById id).mu+7*Lb) := by
    rw [mul_pow,Real.exp_add,show Real.exp (7*Lb) = (Real.exp Lb)^7 by simpa using Real.exp_nat_mul Lb 7]
    ring
  rw [heq] at h
  have he := Real.exp_le_exp.mpr (show -ell*lowMeanFractionReal (fiberTailById id).mu+7*Lb ≤ -fiberTailXA id by linarith only [hguard])
  have hCcoef := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 51/200))
    (by positivity : (0 : ℝ) ≤ (27/40 : ℝ)^7)
  have hCcap := hp.2.1
  have hbound := mul_le_mul (mul_le_mul_of_nonneg_right hCcoef (Real.rpow_pos_of_pos hmup (3/2 : ℝ)).le)
    he (Real.exp_pos _).le (by positivity : 0 ≤ ((51/200 : ℝ)*lowMeanFractionReal (fiberTailById id).C*(27/40 : ℝ)^7)*
      (lowMeanFractionReal (fiberTailById id).mu)^(3/2 : ℝ))
  have hA : fiberTailA id = (51/200 : ℝ)*lowMeanFractionReal (fiberTailById id).C*(27/40 : ℝ)^7 := by
    simp only [fiberTailA,hw]
  have hprice := (fiber_tail_printed_prices id).1
  rw [hA] at hprice
  exact lt_of_le_of_lt (h.trans hbound) hprice

theorem fiber_tail_large_transfer (id : FiberTailIdentity) {q mu rhi b beta ell Lb L : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4 : ℝ) (3/4))
    (hmu : lowMeanFractionReal (fiberTailById id).mu ≤ mu) (hM : 8 ≤ M)
    (hcut : (M : ℝ) < lowMeanFractionReal (fiberTailById id).c*mu)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hC : fiberTailC rhi ≤ lowMeanFractionReal (fiberTailById id).C)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta)
    (hLb : -Real.log (1-q) ≤ Lb) (hL : Lb ≤ L)
    (hrate : lowMeanFractionReal (fiberTailById id).d ≤ ell-lowMeanFractionReal (fiberTailById id).c*L) :
    fiberSpikeTerm q mu ell (fun t => b+beta*(t-1)) M <
      lowMeanFractionReal (fiberTailById id).Z_small := by
  have hp := fiber_tail_real_parameters id
  have hmu0p : 0 < lowMeanFractionReal (fiberTailById id).mu := by linarith only [hp.1]
  have hm := hp.2.2.2.2.2.2.1
  have hCcap := hp.2.1
  have hmp : 0 < lowMeanFractionReal (fiberTailById id).m := by rw [hm]; exact hmu0p.trans_le (le_max_left _ _)
  have hd := hp.2.2.2.2.1.trans_le hrate
  have hdecay : 3/2 ≤ (ell-lowMeanFractionReal (fiberTailById id).c*L)*
      max (lowMeanFractionReal (fiberTailById id).mu) (8/lowMeanFractionReal (fiberTailById id).c) := by
    rw [← hm]
    exact hp.2.2.2.2.2.2.2.trans (mul_le_mul_of_nonneg_right hrate hmp.le)
  have h := fiber_tail_large_price hq hp.1 hmu hM hcut hp.2.2.2.1 hr0 hr1 hr hb hbeta hLb hL hd hdecay
  rw [← hm] at h
  have he := Real.exp_le_exp.mpr (show -(ell-lowMeanFractionReal (fiberTailById id).c*L)*lowMeanFractionReal (fiberTailById id).m ≤
      -lowMeanFractionReal (fiberTailById id).d*lowMeanFractionReal (fiberTailById id).m by
    nlinarith only [mul_le_mul_of_nonneg_right hrate hmp.le])
  have hCcoef : 81*fiberTailC rhi/5000 ≤ (81/5000 : ℝ)*lowMeanFractionReal (fiberTailById id).C := by
    nlinarith only [hC]
  have hbound := mul_le_mul (mul_le_mul_of_nonneg_right hCcoef (Real.rpow_pos_of_pos hmp (3/2 : ℝ)).le)
    he (Real.exp_pos _).le (by positivity : 0 ≤ (81/5000 : ℝ)*lowMeanFractionReal (fiberTailById id).C*
      (lowMeanFractionReal (fiberTailById id).m)^(3/2 : ℝ))
  have hprice := (fiber_tail_printed_prices id).2
  dsimp only [fiberTailB,fiberTailXS] at hprice
  apply lt_of_le_of_lt (h.trans hbound)
  convert hprice using 1 <;> ring

end Erdos993Lean.Analytic.V213
