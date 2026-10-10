module

public import Erdos993Lean.Analytic.V213.FiberTailBounds
public import Erdos993Lean.Analytic.V213.FiberTailLargePrice

/-!
Actual Eq91/Eq92 transfers into the checked printed tail rows.
Ordinary rows use their checked geometric branch; weighted rows use the
least table mean and its guard, never the shifted large-tail mean m.
All hypotheses below are explicit transfer guards, to be discharged by
actual input routing before the final C119/C120 composition.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_tail_real_parameters (id : FiberTailIdentity) :
    let r := fiberTailById id
    (19 : ℝ) ≤ lowMeanFractionReal r.mu ∧
    0 < lowMeanFractionReal r.C ∧ 0 < lowMeanFractionReal r.c ∧
    lowMeanFractionReal r.c ≤ 27/50 ∧ 0 < lowMeanFractionReal r.d ∧
    3/2 ≤ lowMeanFractionReal r.ell * lowMeanFractionReal r.mu ∧
    lowMeanFractionReal r.m = max (lowMeanFractionReal r.mu) (8/lowMeanFractionReal r.c) ∧
    3/2 ≤ lowMeanFractionReal r.d * lowMeanFractionReal r.m := by
  cases id <;> norm_num [fiberTailById,lowMeanFractionReal]

theorem fiber_tail_ordinary_geometric (id : FiberTailIdentity)
    (hnone : (fiberTailById id).weight = none) :
    fiberTailA id = (51/200 : ℝ)*lowMeanFractionReal (fiberTailById id).C*
      max 1 (((27/40 : ℝ)*lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)))^7) := by
  have hf := (fiber_tail_facts id .smallLog).1
  rcases hf with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hbranch⟩
  rw [hnone] at hbranch
  dsimp only at hbranch
  rcases hbranch with ⟨_,_,hvalid,hpos,hgeom,_,_⟩
  have hfactorV : lowMeanFractionValid (lowMeanFractionMul (27,40)
      ((fiberTailById id).h_i.getD (1,1))) := Nat.mul_pos (by norm_num [lowMeanFractionValid]) hvalid
  have hfactor0 : 0 ≤ (27/40 : ℝ)*lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)) := by
    have h := (lowMean_fraction_lt_iff (by norm_num [lowMeanFractionValid]) hvalid).mp hpos
    norm_num [lowMeanFractionReal] at h
    unfold lowMeanFractionReal
    positivity
  dsimp only [fiberTailA]
  rw [hnone]
  by_cases hg : (fiberTailById id).geometricOne = true
  · simp only [hg,ite_true] at hgeom ⊢
    have he := (lowMean_fraction_le_iff hfactorV (by norm_num [lowMeanFractionValid])).mp hgeom
    rw [lowMean_fraction_mul] at he
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Nat.cast_one,Int.cast_one,div_one] at he
    have hp := pow_le_one₀ hfactor0 he (n := 7)
    rw [max_eq_left hp]
  · simp only [hg,Bool.false_eq_true,ite_false] at hgeom ⊢
    have he := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hfactorV).mp hgeom
    rw [lowMean_fraction_mul] at he
    norm_num only [lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Nat.cast_one,Int.cast_one,div_one] at he
    have hp : (1 : ℝ) ≤ ((27/40 : ℝ)*lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)))^7 :=
      one_le_pow₀ he
    rw [max_eq_right hp]

theorem fiber_tail_ordinary_small_transfer (id : FiberTailIdentity)
    (hnone : (fiberTailById id).weight = none) {q mu rhi b beta ell : ℝ} {M : ℕ}
    (hq : q ∈ Set.Icc (1/4 : ℝ) (3/4))
    (hmu : lowMeanFractionReal (fiberTailById id).mu ≤ mu) (hM : M ≤ 7)
    (hr0 : 0 ≤ rhi) (hr1 : rhi < 1) (hr : |fiberSkew q| ≤ rhi)
    (hC : fiberTailC rhi ≤ lowMeanFractionReal (fiberTailById id).C)
    (hb : b ≤ 2/5) (hbeta : 0 ≤ beta)
    (hell : lowMeanFractionReal (fiberTailById id).ell ≤ ell)
    (hhi : 0 < lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)))
    (hL : -Real.log (1-q) ≤ Real.log (lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)))) :
    fiberSpikeTerm q mu ell (fun t => b+beta*(t-1)) M <
      lowMeanFractionReal (fiberTailById id).Z_a := by
  have hp := fiber_tail_real_parameters id
  have hmup : 0 < lowMeanFractionReal (fiberTailById id).mu := by linarith only [hp.1]
  have hdecay : 3/2 ≤ ell*lowMeanFractionReal (fiberTailById id).mu :=
    hp.2.2.2.2.2.1.trans (mul_le_mul_of_nonneg_right hell hmup.le)
  have h := fiber_tail_small_price hq hp.1 hmu hM hr0 hr1 hr hb hbeta hL hdecay
  rw [Real.exp_log hhi] at h
  have he : Real.exp (-ell*lowMeanFractionReal (fiberTailById id).mu) ≤
      Real.exp (-lowMeanFractionReal (fiberTailById id).ell*lowMeanFractionReal (fiberTailById id).mu) :=
    Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_right hell hmup.le])
  have hCp := fiber_tail_C_pos hr0 hr1
  have hcoef : 0 ≤ (51*fiberTailC rhi/200) := by positivity
  have hcoef' : 51*fiberTailC rhi/200 ≤ (51/200 : ℝ)*lowMeanFractionReal (fiberTailById id).C := by
    nlinarith only [hC]
  have hCcap := hp.2.1
  have hpow := (Real.rpow_pos_of_pos hmup (3/2 : ℝ)).le
  have hmax : 0 ≤ max 1 (((27/40 : ℝ)*lowMeanFractionReal ((fiberTailById id).h_i.getD (1,1)))^7) :=
    le_trans (by norm_num) (le_max_left _ _)
  have hbound := mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hcoef' hpow) he (Real.exp_pos _).le
      (by positivity : 0 ≤ (51/200 : ℝ)*lowMeanFractionReal (fiberTailById id).C*
        (lowMeanFractionReal (fiberTailById id).mu)^(3/2 : ℝ))) hmax
  have hprice := (fiber_tail_printed_prices id).1
  have hxa : fiberTailXA id = lowMeanFractionReal (fiberTailById id).mu * lowMeanFractionReal (fiberTailById id).ell := by
    simp only [fiberTailXA,hnone]
  rw [fiber_tail_ordinary_geometric id hnone,hxa] at hprice
  apply lt_of_le_of_lt (h.trans hbound)
  convert hprice using 1 <;> ring

end Erdos993Lean.Analytic.V213
