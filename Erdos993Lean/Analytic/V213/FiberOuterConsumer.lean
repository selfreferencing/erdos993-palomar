module

public import Erdos993Lean.Analytic.V213.FiberOuterSkewMonotonicity

/-!
Exact actual-fiber outer envelope F/B>=U_N(r^2;t).
This uses the actual all-integer Eq77 and constrained minimum. The only
rate guard is the printed R_N>0; no support, Gaussian bound or numerical
start premise remains. The original q and actual integer rank are kept.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_outer_P_positive {N r : ℝ} (hN : 17 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 < fiberOuterP N (r ^ 2) := by
  have hm : 11 ≤ N + 1 := by linarith only [hN]
  have hn : 0 < N + 1 := by linarith only [hN]
  have hd := fiber_gain_D_lower hm
  have hD : 0 < fiberGainD (N + 1) := (by positivity : (0 : ℝ) < 439 / (180 * (N + 1))).trans_le hd
  have hc := fiber_gain_C_lower hr0 hrh hm
  have hC : 0 ≤ fiberGainC r (N + 1) := by
    have hl := fiber_gain_C_half_lower hm
    have hp : (0 : ℝ) ≤ 769 / 891 := by norm_num
    exact hp.trans (hl.trans hc)
  rw [fiber_outer_P_square]
  exact add_pos_of_pos_of_nonneg hD (mul_nonneg (sq_nonneg r) hC)

theorem fiber_outer_Delta_nonneg {N r : ℝ} (hN : 17 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 ≤ fiberOuterDelta N (r ^ 2) := by
  have hn : 0 < N := by linarith only [hN]
  have ha : 0 < 1 - r ^ 2 := by nlinarith only [hr0,hrh]
  have hh : 0 ≤ N - 1 + 1 / N := by
    have hi : 0 ≤ 1 / N := by positivity
    linarith only [hN,hi]
  unfold fiberOuterDelta
  exact mul_nonneg (div_nonneg (sq_nonneg r) ha.le) hh

theorem fiber_outer_actual_envelope {M : ℕ} {q mu : ℝ}
    (hN : 17 ≤ (M : ℝ) + 2) (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4)
    (hmu : 0 < mu) (hR : 0 < fiberOuterR ((M : ℝ) + 2) (fiberSkew q ^ 2))
    (j : ℤ) (hw : fiberBonus q M ≤ fiberSquareOffset q M j) :
    fiberOuterU ((M : ℝ) + 2) (fiberSkew q ^ 2) ((M : ℝ) / mu) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith only [hq0]
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith only [hqh]
  have hDelta := fiber_outer_delta_actual (by linarith only [hN] : 0 < (M : ℝ) + 2) hr0 hrh
  have hb := fiber_upper_envelope_parameters (N0 := 17) (by norm_num) hN hq0 hqh hmu
    (fiber_outer_P_positive hN hr0 hrh) hR (fiber_outer_Delta_nonneg hN hr0 hrh)
    (fiber_outer_R_actual hN hr0 hrh) hDelta.le (fiber_outer_P_actual hN hr0 hrh) j hw
  simpa only [fiberEndpointUpper,fiberEndpointLambda,fiberOuterU] using hb

end Erdos993Lean.Analytic.V213
