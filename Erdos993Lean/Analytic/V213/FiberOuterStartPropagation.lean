module

public import Erdos993Lean.Analytic.V213.FiberOuterStartGuards
public import Erdos993Lean.Analytic.V213.FiberOuterConsumer

/-!
Actual endpoint propagation from the four printed F05 start rows.
Every numerical guard is obtained from the named Int/Nat checker. The
endpoint principle uses the global positive-t supremum and both target
signs. Monotonicity then covers every real N and the closed skew region.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_outer_envelope_parameter_lower {N y p d R t : ℝ}
    (hR : 0 < R) (hRb : R ≤ fiberOuterR N y)
    (hdb : d ≤ fiberOuterDelta N y) (hpb : p ≤ fiberOuterP N y) :
    fiberEndpointUpper p d R t ≤ fiberOuterU N y t := by
  have hRa : 0 < fiberOuterR N y := hR.trans_le hRb
  have hg := shared_G_antitoneOn_nonpos (min_le_left (0 : ℝ) _)
    (min_le_left (0 : ℝ) _) (min_le_min_left (0 : ℝ)
      (by linarith only [hpb] : (5 / 2 : ℝ) * log t + p ≤ 5 / 2 * log t + fiberOuterP N y))
  have hc : 2 / fiberOuterR N y ≤ 2 / R :=
    div_le_div_of_nonneg_left (by norm_num) hR hRb
  have hl := mul_le_mul hg hc (by positivity : 0 ≤ 2 / fiberOuterR N y)
    (shared_G_nonneg (min 0 ((5 / 2 : ℝ) * log t + p)))
  unfold fiberEndpointUpper fiberEndpointLambda fiberOuterU
  linarith only [hl,hdb]

theorem fiber_outer_named_endpoint_start (id : FiberOuterStartIdentity)
    {b beta : ℝ} (hb : b ≤ lowMeanFractionReal (fiberOuterStartById id).b0)
    (hbeta : lowMeanFractionReal (fiberOuterStartById id).beta0 ≤ beta) :
    let r := fiberOuterStartById id
    let n := lowMeanFractionReal r.n
    let sigma := lowMeanFractionReal r.sigma
    max (fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) sigma)
      (((n - 2) / n) * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) sigma) ≤
      fiberEndpointUpper (lowMeanFractionReal r.p_star) (lowMeanFractionReal r.d_star)
        (lowMeanFractionReal r.R_star) sigma := by
  let r := fiberOuterStartById id
  let n := lowMeanFractionReal r.n
  let sigma := lowMeanFractionReal r.sigma
  let p := lowMeanFractionReal r.p_star
  let d := lowMeanFractionReal r.d_star
  let R := lowMeanFractionReal r.R_star
  let v := lowMeanFractionReal r.v_star
  let f0 := fiberEndpointTarget (10 + lowMeanFractionReal r.beta0)
    (9 / 2 + lowMeanFractionReal r.beta0 - lowMeanFractionReal r.b0) sigma
  have hn := fiber_outer_start_guard_sound id .nMin
  have hs := fiber_outer_start_guard_sound id .sigmaPos
  have hsh := fiber_outer_start_guard_sound id .sigmaMax
  have hR := fiber_outer_start_guard_sound id .RPos
  have hv0 := fiber_outer_start_guard_sound id .vMin
  have hv3 := fiber_outer_start_guard_sound id .vMax
  have homega := fiber_outer_start_guard_sound id .omegaMax
  change 17 ≤ n at hn
  change 0 < sigma at hs
  change sigma < 1 at hsh
  change 0 < R at hR
  change 0 ≤ v at hv0
  change v < 3 at hv3
  change 5 / 2 * lowMeanFractionReal r.logUpper - p ≤ v at homega
  have hlog := (fiber_outer_log_sigma hs hsh.le).trans (fiber_outer_start_log id)
  change -log sigma ≤ lowMeanFractionReal r.logUpper at hlog
  have hlambda : -v ≤ fiberEndpointLambda p sigma := by
    unfold fiberEndpointLambda
    linarith only [hlog,homega]
  have hbar := fiber_outer_endpoint_barrier_lower (d := d) hR hv0 hv3.le hlambda
  have hg := (fiber_outer_start_gap id).2
  change 1 / 40 < 1 + d - 2 * (v ^ 2 / (4 - v + v ^ 2 / 48)) / R - ((n - 2) / n) * f0 at hg
  have hf0 := (fiber_outer_start_target id).2
  change f0 < 0 at hf0
  have heta0 : 0 ≤ (n - 2) / n := div_nonneg (by linarith only [hn]) (by linarith only [hn])
  have heta1 : (n - 2) / n ≤ 1 := (div_le_one (by linarith only [hn] : 0 < n)).2 (by linarith)
  have ht := fiber_outer_target_start_order hs hsh.le hb hbeta
  have htmax := fiber_outer_signed_negative_start heta0 heta1 ht hf0
  exact htmax.trans (by linarith only [hg,hbar])

theorem fiber_outer_named_endpoint_propagation (id : FiberOuterStartIdentity)
    {b beta t : ℝ} (hb : b ≤ lowMeanFractionReal (fiberOuterStartById id).b0)
    (hbeta : lowMeanFractionReal (fiberOuterStartById id).beta0 ≤ beta)
    (hbetah : beta ≤ 1) (ht : lowMeanFractionReal (fiberOuterStartById id).sigma ≤ t) :
    let r := fiberOuterStartById id
    let n := lowMeanFractionReal r.n
    max (fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t)
      (((n - 2) / n) * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t) ≤
      fiberOuterU n (lowMeanFractionReal r.a ^ 2) t := by
  let r := fiberOuterStartById id
  let n := lowMeanFractionReal r.n
  let p := lowMeanFractionReal r.p_star
  let d := lowMeanFractionReal r.d_star
  let R := lowMeanFractionReal r.R_star
  have hn := fiber_outer_start_guard_sound id .nMin
  have hp := fiber_outer_start_guard_sound id .pMin
  have hd := fiber_outer_start_guard_sound id .dMin
  have hR := fiber_outer_start_guard_sound id .RPos
  have hs := fiber_outer_start_guard_sound id .sigmaPos
  have hbmax := fiber_outer_start_guard_sound id .bMax
  have hbta := fiber_outer_start_guard_sound id .betaMin
  change 17 ≤ n at hn
  change 1 / 6 < p at hp
  change 1 / 2 < d at hd
  change 0 < R at hR
  change 0 < lowMeanFractionReal r.sigma at hs
  change lowMeanFractionReal r.b0 ≤ 2 / 5 at hbmax
  change 0 ≤ lowMeanFractionReal r.beta0 at hbta
  have hb' : b ≤ 2 / 5 := hb.trans hbmax
  have hbeta' : 0 ≤ beta := hbta.trans hbeta
  have heta0 : 0 < (n - 2) / n := div_pos (by linarith only [hn]) (by linarith only [hn])
  have heta1 : (n - 2) / n ≤ 1 := (div_le_one (by linarith only [hn] : 0 < n)).2 (by linarith)
  have hc : 0 < 9 / 2 + beta - b := by linarith only [hb',hbeta']
  have hcap := (fiber_outer_target_supremum hb' hbeta' hbetah).2.le.trans
    (by linarith only [hd] : (3 / 2 : ℝ) ≤ 1 + d)
  have hprop := fiber_endpoint_principle (by linarith only [hp]) hR (by linarith only [hd])
    heta0 heta1 (by linarith only [hbeta'] : 0 < 10 + beta) hc hs
    (fiber_outer_endpoint_cutoff hp hb' hbeta').2 hcap (fiber_outer_named_endpoint_start id hb hbeta) t ht
  have hparam := fiber_outer_envelope_parameter_lower (t := t) (N := n) (y := lowMeanFractionReal r.a ^ 2)
    hR (fiber_outer_start_rate id) (fiber_outer_start_bonus id) (fiber_outer_start_gain id).le
  exact hprop.trans hparam

theorem fiber_outer_named_region (id : FiberOuterStartIdentity)
    {N r b beta t : ℝ} (hN : lowMeanFractionReal (fiberOuterStartById id).n ≤ N)
    (hra : lowMeanFractionReal (fiberOuterStartById id).a ≤ r) (hrh : r ≤ 2 / 5)
    (hb : b ≤ lowMeanFractionReal (fiberOuterStartById id).b0)
    (hbeta : lowMeanFractionReal (fiberOuterStartById id).beta0 ≤ beta) (hbetah : beta ≤ 1)
    (ht : lowMeanFractionReal (fiberOuterStartById id).sigma ≤ t) :
    let n := lowMeanFractionReal (fiberOuterStartById id).n
    max (fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t)
      (((n - 2) / n) * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) t) ≤
      fiberOuterU N (r ^ 2) t := by
  let n := lowMeanFractionReal (fiberOuterStartById id).n
  let a := lowMeanFractionReal (fiberOuterStartById id).a
  have hn := fiber_outer_start_guard_sound id .nMin
  have ha := fiber_outer_start_guard_sound id .aPos
  have hah := fiber_outer_start_guard_sound id .aMax
  have hna := fiber_outer_start_guard_sound id .naMin
  change 17 ≤ n at hn
  change 0 < a at ha
  change a ≤ 2 / 5 at hah
  change 18 / 5 ≤ (n + 1) * a at hna
  have hwidth := (fiber_outer_U_increases_N ha hah hn hna t).monotoneOn
    (show n ∈ Ici n from le_rfl) hN hN
  have hy : a ^ 2 ≤ r ^ 2 := by nlinarith only [ha,hra]
  have hya : a ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith only [ha,hah]
  have hyr : r ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith only [ha,hra,hrh]
  have hskew := (fiber_outer_U_increases_y (hn.trans hN) t).monotoneOn
    ⟨sq_nonneg a,hya⟩ ⟨sq_nonneg r,hyr⟩ hy
  exact (fiber_outer_named_endpoint_propagation id hb hbeta hbetah ht).trans (hwidth.trans hskew)

end Erdos993Lean.Analytic.V213
