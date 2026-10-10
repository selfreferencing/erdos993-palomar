module

public import Erdos993Lean.Analytic.V213.FiberBudgetInputCheck
public import Erdos993Lean.Analytic.V213.FiberPriceCheck

/-!
Real consequences of all55 actual input-to-block checks. Both
accepted N44 endpoints define the whole closed absolute-skew bound.
The actual Part1 D, theta and mean and the actual F16 price are retained;
there is no second list of55 margins.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_budget_input_parameters (id : FiberInputIdentity) :
    let r := fiberBudgetById (fiberInputBudget id)
    let p := fiberInputPaperRow id
    lowMeanFractionReal p.mu0 = lowMeanFractionReal (fiberInputRouteById id).mu0 ∧
    lowMeanFractionReal r.b = lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind) ∧
    lowMeanFractionReal r.mu_star ≤ lowMeanFractionReal (fiberInputRouteById id).mu0 ∧
    lowMeanFractionReal p.theta ≤ lowMeanFractionReal r.Theta ∧
    lowMeanFractionReal p.D ≤ lowMeanFractionReal r.D_star ∧
    fiberInputSkewHigh (lowMeanFractionReal (fiberInputQloFraction id))
      (lowMeanFractionReal (fiberInputQhiFraction id)) ≤ lowMeanFractionReal r.R ∧
    lowMeanFractionReal (fiberInputPriceFraction id) ≤ lowMeanFractionReal r.Z ∧
    lowMeanFractionReal r.R ≤ 1/2 ∧
    0 ≤ lowMeanFractionReal p.D ∧ 0 ≤ lowMeanFractionReal p.theta := by
  dsimp only
  rcases fiber_budget_input_facts id with ⟨_,_,hpm,hpt,hpd,hlv,hhv,hme,hbe,hmu,ht,hD,hl,hh,hz,hR,hD0,ht0⟩
  rcases fiber_budget_parameters (fiberInputBudget id) with
    ⟨_,_,hmv,hbv,htv,hDv,hRv,_,hzv,_,_,_,_,_,_,_,_⟩
  have hd := fiber_input_domain_facts id
  have him := hd.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hib : lowMeanFractionValid (fiberInputClassB (fiberInputRouteById id).kind) := by
    cases id <;> decide +kernel
  have hiz := fiber_price_valid id
  have hme' := (lowMean_fraction_eq_iff hpm him).mp hme
  have hbe' := (lowMean_fraction_eq_iff hbv hib).mp hbe
  have hmu' := (lowMean_fraction_le_iff hmv him).mp hmu
  have ht' := (lowMean_fraction_le_iff hpt htv).mp ht
  have hD' := (lowMean_fraction_le_iff hpd hDv).mp hD
  have hla : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction (fiberInputQloFraction id))) := hlv
  have hha : lowMeanFractionValid (lowMeanFractionAbs (fiberInputSignedSkewFraction (fiberInputQhiFraction id))) := hhv
  have hl' := (lowMean_fraction_le_iff hla hRv).mp hl
  have hh' := (lowMean_fraction_le_iff hha hRv).mp hh
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.1] at hl'
  rw [lowMean_fraction_abs,fiber_input_signed_skew_real hd.2.2.2.1] at hh'
  have hz' := (lowMean_fraction_le_iff hiz hzv).mp hz
  have hR' := (lowMean_fraction_le_iff hRv (by norm_num [lowMeanFractionValid])).mp hR
  have hD0' := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hpd).mp hD0
  have ht0' := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hpt).mp ht0
  norm_num only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div,Int.cast_one,Nat.cast_ofNat] at hR' hD0' ht0'
  exact ⟨hme',hbe',hmu',ht',hD',max_le hl' hh',hz',hR',hD0',ht0'⟩

theorem fiber_budget_real_parameters (id : FiberBudgetIdentity) :
    0 < lowMeanFractionReal (fiberBudgetById id).mu_star ∧
    0 ≤ lowMeanFractionReal (fiberBudgetById id).R ∧
    lowMeanFractionReal (fiberBudgetById id).R < 1 ∧
    0 ≤ lowMeanFractionReal (fiberBudgetById id).D_star ∧
    0 ≤ lowMeanFractionReal (fiberBudgetById id).Theta := by
  rcases fiber_budget_parameters id with ⟨_,_,hm,_,ht,hD,hR,_,_,_,_,hmp,hR0,hR1,hD0,ht0,_⟩
  have hm' := (lowMean_fraction_lt_iff (by norm_num [lowMeanFractionValid]) hm).mp hmp
  have hR0' := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hR).mp hR0
  have hR1' := (lowMean_fraction_lt_iff hR (by norm_num [lowMeanFractionValid])).mp hR1
  have hD0' := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) hD).mp hD0
  have ht0' := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) ht).mp ht0
  norm_num only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div,Int.cast_one,one_div] at hm' hR0' hR1' hD0' ht0'
  exact ⟨hm',hR0',hR1',hD0',ht0'⟩

end Erdos993Lean.Analytic.V213
