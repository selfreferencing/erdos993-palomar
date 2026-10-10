module

public import Erdos993Lean.Analytic.V213.FiberCoupledRates

/-!
Exact actual-rate positivity on all six C1/C2 input intervals.
The coupled function is applied to the actual upper endpoint. The first
input may start below .36; no coupled-domain assertion is made at its
arbitrary activity.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_coupled_input_transfer {base slope ell z lambda t ts : ℝ}
    (hell : base+slope*z ≤ ell) (hlambda : 0 ≤ lambda) (hh : lambda ≤ z)
    (ht0 : 0 ≤ t) (ht : t ≤ ts) :
    fiberCoupledRate base slope ts z ≤ ell-Real.log (1+lambda)*t := by
  have hz : 0 ≤ z := hlambda.trans hh
  have hlog := Real.log_le_log (by linarith only [hlambda] : 0 < 1+lambda)
    (show 1+lambda ≤ 1+z by linarith only [hh])
  have hlog0 : 0 ≤ Real.log (1+z) := Real.log_nonneg (by linarith only [hz])
  have hm1 := mul_le_mul_of_nonneg_right hlog ht0
  have hm2 := mul_le_mul_of_nonneg_left ht hlog0
  unfold fiberCoupledRate
  linarith only [hell,hm1,hm2]

theorem fiber_coupled_input_rate_positive (id : FiberCornerRateIdentity) {lambda t : ℝ}
    (hlambda : 0 ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction (fiberCornerRateById id).input))
    (ht0 : 0 ≤ t)
    (ht : t ≤ lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ts) :
    0 < lowMeanFractionReal (fiberInputRouteById (fiberCornerRateById id).input).ell0 - Real.log (1+lambda)*t := by
  have hf := fiber_corner_rate_facts id
  rcases hf with ⟨hpr,hi,he,hhi,hb,hs,heV,hhV,hpos,hval⟩
  have hslack := fiber_corner_rate_bound id
  dsimp only at hslack
  have hhiR := congrArg lowMeanFractionReal hhi
  rw [← hhiR] at hh hslack
  have htransfer := fiber_coupled_input_transfer hslack.le hlambda hh ht0 ht
  cases id with
  | iota0 =>
    have hc := fiber_c1_coupled_lower (z := 9/25) (c := 3/5) (by norm_num) (Or.inr rfl)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 279/1000-(929/2500)*(3/5) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)
  | iota1 =>
    have hc := fiber_c1_coupled_lower (z := 2/5) (c := 3/5) (by norm_num) (Or.inr rfl)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 279/1000-(929/2500)*(3/5) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)
  | iota2 =>
    have hc := fiber_c1_coupled_lower (z := 9/20) (c := 3/5) (by norm_num) (Or.inr rfl)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 279/1000-(929/2500)*(3/5) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)
  | iota3 =>
    have hc := fiber_c2_time_coupled_lower (z := 1/2) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 423/1250-(471/1000)*(69/100) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)
  | iota4 =>
    have hc := fiber_c2_time_coupled_lower (z := 11/20) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 423/1250-(471/1000)*(69/100) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)
  | iota5 =>
    have hc := fiber_c2_time_coupled_lower (z := 3/5) (by norm_num)
    norm_num [fiberCornerRateById,fiberInputRouteById,lowMeanFractionReal] at htransfer ⊢
    have hp : (0 : ℝ) < 423/1250-(471/1000)*(69/100) := by norm_num
    exact sub_pos.mp ((hp.trans_le hc).trans_le htransfer)

end Erdos993Lean.Analytic.V213
