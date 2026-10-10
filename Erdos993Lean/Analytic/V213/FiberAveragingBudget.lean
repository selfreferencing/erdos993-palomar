module

public import Erdos993Lean.Analytic.V213.FiberBudgetInputParameters

/-!
Actual per-input epsilon, defined from the accepted input and
F16 records rather than a second list of55 values. The rational budget
comparisons extend to every real mean above the actual starting mean.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberInputEpsilon (id : FiberInputIdentity) : ℝ :=
  let p := fiberInputPaperRow id
  let mu0 := lowMeanFractionReal (fiberInputRouteById id).mu0
  let rhi := fiberInputSkewHigh (lowMeanFractionReal (fiberInputQloFraction id))
    (lowMeanFractionReal (fiberInputQhiFraction id))
  1+lowMeanFractionReal (fiberInputClassB (fiberInputRouteById id).kind)-lowMeanFractionReal p.theta-
    9*lowMeanFractionReal p.D/(2*mu0)-rhi^2/((1-rhi^2)*mu0)-
    lowMeanFractionReal (fiberInputPriceFraction id)

theorem fiber_averaging_cost_mean_mono {D r mu nu : ℝ}
    (hD : 0 ≤ D) (hr : 0 ≤ r) (hrh : r ≤ 1/2) (hnu : 0 < nu) (hm : nu ≤ mu) :
    9*D/(2*mu) ≤ 9*D/(2*nu) ∧
    r^2/((1-r^2)*mu) ≤ r^2/((1-r^2)*nu) := by
  have ho : 0 < 1-r^2 := by nlinarith only [hr,hrh]
  constructor
  · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith only [hm])
  · exact div_le_div_of_nonneg_left (sq_nonneg r) (mul_pos ho hnu)
      (mul_le_mul_of_nonneg_left hm ho.le)

theorem fiber_input_epsilon_block (id : FiberInputIdentity) :
    fiberBlockBudget (fiberInputBudget id)-lowMeanFractionReal (fiberBudgetById (fiberInputBudget id)).Z ≤
      fiberInputEpsilon id := by
  rcases fiber_budget_input_parameters id with ⟨_,hb,hm,ht,hD,hr,hz,hRh,hD0,_⟩
  rcases fiber_budget_real_parameters (fiberInputBudget id) with ⟨hmp,hR0,_,hDs,_⟩
  have hm0 := fiber_input_starting_mean_positive id
  have hr0 := fiber_skew_high_nonneg (lowMeanFractionReal (fiberInputQloFraction id))
    (lowMeanFractionReal (fiberInputQhiFraction id))
  have hcost := fiber_averaging_cost_mean_mono hDs hR0 hRh hmp hm
  have hDcost : 9*lowMeanFractionReal (fiberInputPaperRow id).D/
      (2*lowMeanFractionReal (fiberInputRouteById id).mu0) ≤
      9*lowMeanFractionReal (fiberBudgetById (fiberInputBudget id)).D_star/
      (2*lowMeanFractionReal (fiberInputRouteById id).mu0) := by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by norm_num)) (by positivity)
  have hratio := fiber_skew_ratio_monotone hr0 hr hRh
  have hrCost := div_le_div_of_nonneg_right hratio hm0.le
  simp only [div_div] at hrCost
  unfold fiberInputEpsilon fiberBlockBudget
  dsimp only
  linarith only [hb,ht,hz,hDcost,hrCost,hcost.1,hcost.2]

theorem fiber_input_epsilon_strict (id : FiberInputIdentity) :
    (1/500 : ℝ) < fiberInputEpsilon id := by
  have hb := fiber_budget_all_thirteen (fiberInputBudget id)
  have he := fiber_input_epsilon_block id
  linarith only [hb.1,hb.2.1,he]

end Erdos993Lean.Analytic.V213
