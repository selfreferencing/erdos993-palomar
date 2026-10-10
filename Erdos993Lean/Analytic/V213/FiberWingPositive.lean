module

public import Erdos993Lean.Analytic.V213.FiberWingParameters
public import Erdos993Lean.Analytic.V213.FiberWingEndpoint
public import Erdos993Lean.Analytic.V213.FiberUpperEnvelope
public import Erdos993Lean.Analytic.V213.FiberLowerBranches

/-!
The actual positive-skew wing comparison. All start, coefficient,
width, global-supremum and endpoint hypotheses are discharged by the
named accepted F04 rows and the real Eq86/87 proofs. The full closed
interval tau<=t<=3/5 includes the lower-offset equality seam.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

theorem fiber_wing_positive_comparison (id : FiberWingIdentity) {q mu : ℝ}
    (hmu : lowMeanFractionReal (fiberWingById id).mu_W ≤ mu)
    (hqlo : lowMeanFractionReal (fiberWingById id).skew_lower ≤ fiberSkew q)
    (hqhi : fiberSkew q ≤ lowMeanFractionReal (fiberWingById id).skew_upper)
    (M : ℕ) (j : ℤ) (htlo : lowMeanFractionReal (fiberWingById id).tau ≤ (M : ℝ) / mu)
    (hthi : (M : ℝ) / mu ≤ 3 / 5) :
    fiberPsi ((M : ℝ) / mu) ≤ fiberF q mu M j := by
  have hmu0 := fiber_wing_guard_sound id .muPos
  have hmu19 := fiber_wing_guard_sound id .muMin
  have htau := fiber_wing_guard_sound id .tauPos
  have hskew0 := fiber_wing_guard_sound id .skewPos
  have hskewh := fiber_wing_guard_sound id .skewMax
  change 0 < lowMeanFractionReal (fiberWingById id).mu_W at hmu0
  change 19 ≤ lowMeanFractionReal (fiberWingById id).mu_W at hmu19
  change 0 < lowMeanFractionReal (fiberWingById id).tau at htau
  change 0 < lowMeanFractionReal (fiberWingById id).skew_lower at hskew0
  change lowMeanFractionReal (fiberWingById id).skew_upper ≤ 1 / 2 at hskewh
  have hmupos := hmu0.trans_le hmu
  have hq0 : 1 / 2 ≤ q := by unfold fiberSkew at hqlo; linarith only [hqlo,hskew0]
  have hqh : q ≤ 3 / 4 := by unfold fiberSkew at hqhi; linarith only [hqhi,hskewh]
  have htpos := htau.trans_le htlo
  by_cases hw : fiberSquareOffset q M j ≤ fiberBonus q M
  · have hl := fiber_lower_small_ratio (by linarith : 0 < q) (by linarith : q < 1)
      (hmu19.trans hmu) M j hw hthi
    have hmargin : 0 < 1 / (4 * mu) := by positivity
    linarith only [hl,hmargin]
  · have hn := fiber_wing_start_width id hmu htlo
    have hcancel : mu * ((M : ℝ) / mu) = (M : ℝ) := by field_simp [hmupos.ne']
    rw [hcancel] at hn
    have hn0 := fiber_wing_guard_sound id .nMin
    have hp := fiber_wing_guard_sound id .pPos
    have hd := fiber_wing_guard_sound id .dPos
    have hR := fiber_wing_guard_sound id .RPos
    change 13 ≤ lowMeanFractionReal (fiberWingById id).N0 at hn0
    change 0 < lowMeanFractionReal (fiberWingById id).p at hp
    change 0 < lowMeanFractionReal (fiberWingById id).d at hd
    change 0 < lowMeanFractionReal (fiberWingById id).R at hR
    have hparams := fiber_wing_actual_parameters id hn hqlo hqhi
    have hcap : sSup ((fiberEndpointTarget 10 (9 / 2)) '' Ioi 0) ≤
        1 + lowMeanFractionReal (fiberWingById id).d := by
      rw [fiber_wing_target_supremum]
      linarith only [hd]
    have he := fiber_upper_endpoint_comparison (by linarith : 10 ≤ lowMeanFractionReal (fiberWingById id).N0)
      hn hq0 hqh hmupos hp hR hd.le (by norm_num : (0 : ℝ) < 10)
      (by norm_num : (0 : ℝ) < 9 / 2) htau hparams.1 hparams.2.1 hparams.2.2
      (fiber_wing_endpoint_cutoff hp.le) hcap (fiber_wing_endpoint_start id) j
      (le_of_lt (lt_of_not_ge hw)) htlo
    have hi : (M : ℝ) / mu * fiberEndpointTarget 10 (9 / 2) ((M : ℝ) / mu) =
        fiberPsi ((M : ℝ) / mu) := by
      have h := fiber_outer_target_identity htpos 0 0
      simpa only [add_zero,sub_zero,zero_mul] using h
    rw [hi] at he
    exact he

end Erdos993Lean.Analytic.V213
