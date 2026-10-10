module

public import Erdos993Lean.Analytic.V213.FiberWingGuards
public import Erdos993Lean.Analytic.V213.FiberWingRate
public import Erdos993Lean.Analytic.V213.FiberWingGain

/-!
The actual rho_U, Delta and Phi bounds of all three printed wing
rows over every real N>=N0 and the entire closed printed skew interval.
The improved coefficient is used for W1/W2. Source square-root and width
checks are interpreted as real inequalities, not assumed parameters.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real

theorem fiber_wing_actual_parameters (id : FiberWingIdentity) {N r : ℝ}
    (hN : lowMeanFractionReal (fiberWingById id).N0 ≤ N)
    (hrl : lowMeanFractionReal (fiberWingById id).skew_lower ≤ r)
    (hrh : r ≤ lowMeanFractionReal (fiberWingById id).skew_upper) :
    lowMeanFractionReal (fiberWingById id).R ≤ V22.rhoU r N ∧
      lowMeanFractionReal (fiberWingById id).d ≤ V22.Delta r N ∧
      lowMeanFractionReal (fiberWingById id).p ≤ V22.phiR r N := by
  have hn0 := fiber_wing_guard_sound id .nMin
  have ha := fiber_wing_guard_sound id .aPos
  have hab := fiber_wing_guard_sound id .aSkew
  have hrb := fiber_wing_guard_sound id .skewB
  have hbh := fiber_wing_guard_sound id .bMax
  change 13 ≤ lowMeanFractionReal (fiberWingById id).N0 at hn0
  change 0 < lowMeanFractionReal (fiberWingById id).a at ha
  change lowMeanFractionReal (fiberWingById id).a ≤ lowMeanFractionReal (fiberWingById id).skew_lower at hab
  change lowMeanFractionReal (fiberWingById id).skew_upper ≤ lowMeanFractionReal (fiberWingById id).b at hrb
  change lowMeanFractionReal (fiberWingById id).b ≤ 1 / 5 at hbh
  have har := hab.trans hrl
  have hrb' := hrh.trans hrb
  have hr0 := ha.trans_le har
  have hroot := fiber_wing_rootSquare_checked id
  have hS := fiber_wing_guard_sound id .sqrtPos
  change 0 < lowMeanFractionReal (fiberWingById id).sqrtUpper at hS
  change 0 ≤ (lowMeanFractionReal (fiberWingById id).sqrtUpper) ^ 2 -
      lowMeanFractionReal (fiberWingById id).N0 at hroot
  have hsqrt : Real.sqrt (lowMeanFractionReal (fiberWingById id).N0) ≤
      lowMeanFractionReal (fiberWingById id).sqrtUpper :=
    Real.sqrt_le_iff.2 ⟨hS.le,by linarith only [hroot]⟩
  have hb0 : 0 ≤ lowMeanFractionReal (fiberWingById id).b := hr0.le.trans hrb'
  have hnp : 0 < lowMeanFractionReal (fiberWingById id).N0 + 1 := by linarith only [hn0]
  have hu := fiber_wing_rate_uniform hn0 hN hr0 hrb' hbh
  have hmult := mul_le_mul_of_nonneg_left hsqrt
    (by positivity : 0 ≤ 2 * lowMeanFractionReal (fiberWingById id).b /
      (lowMeanFractionReal (fiberWingById id).N0 + 1))
  have hmult' : 2 * lowMeanFractionReal (fiberWingById id).b *
      Real.sqrt (lowMeanFractionReal (fiberWingById id).N0) /
      (lowMeanFractionReal (fiberWingById id).N0 + 1) ≤
      2 * lowMeanFractionReal (fiberWingById id).b * lowMeanFractionReal (fiberWingById id).sqrtUpper /
        (lowMeanFractionReal (fiberWingById id).N0 + 1) := by
    convert hmult using 1 <;> ring
  have hrv : fiberWingValue id .rate ≤ V22.rhoU r N := by
    unfold fiberWingValue
    dsimp only
    linarith only [hu,hmult']
  have hd := fiber_wing_bonus_uniform hn0 hN ha har (hrb'.trans hbh)
  have hdv : fiberWingValue id .bonus ≤ V22.Delta r N := hd
  have hgain : fiberWingValue id .gain ≤ V22.phiR r N := by
    have hiA := fiber_wing_guard_sound id .aImproved
    have hiB := fiber_wing_guard_sound id .bImproved
    cases id with
    | w1 =>
      have hp := fiber_wing_gain_improved (hn0.trans hN) (by exact hiA) har hrb' (by exact hiB)
      convert hp using 1 <;> simp only [fiberWingValue,fiberWingById,lowMeanFractionReal,
        Int.cast_ofNat,Nat.cast_ofNat] <;> ring
    | w2 =>
      have hp := fiber_wing_gain_improved (hn0.trans hN) (by exact hiA) har hrb' (by exact hiB)
      convert hp using 1 <;> simp only [fiberWingValue,fiberWingById,lowMeanFractionReal,
        Int.cast_ofNat,Nat.cast_ofNat] <;> ring
    | w3 =>
      have hp := fiber_wing_gain_uniform (hn0.trans hN) ha har hrb' hbh
      convert hp using 1 <;> simp only [fiberWingValue,fiberWingById,lowMeanFractionReal,
        Int.cast_ofNat,Nat.cast_ofNat] <;> ring
  exact ⟨(fiber_wing_rate_checked id).trans hrv,
    (fiber_wing_bonus_checked id).trans hdv,(fiber_wing_gain_checked id).trans hgain⟩

theorem fiber_wing_start_width (id : FiberWingIdentity) {mu t : ℝ}
    (hmu : lowMeanFractionReal (fiberWingById id).mu_W ≤ mu)
    (ht : lowMeanFractionReal (fiberWingById id).tau ≤ t) :
    lowMeanFractionReal (fiberWingById id).N0 ≤ mu * t + 2 := by
  have hm := fiber_wing_guard_sound id .muPos
  have hp := fiber_wing_guard_sound id .tauPos
  change 0 < lowMeanFractionReal (fiberWingById id).mu_W at hm
  change 0 < lowMeanFractionReal (fiberWingById id).tau at hp
  have hprod := mul_le_mul hmu ht hp.le (hm.trans_le hmu).le
  have hw := fiber_wing_width_checked id
  change 0 ≤ lowMeanFractionReal (fiberWingById id).mu_W *
    lowMeanFractionReal (fiberWingById id).tau + 2 - lowMeanFractionReal (fiberWingById id).N0 at hw
  linarith only [hprod,hw]

end Erdos993Lean.Analytic.V213
