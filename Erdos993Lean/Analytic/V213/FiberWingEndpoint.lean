module

public import Erdos993Lean.Analytic.V213.FiberWingGuards
public import Erdos993Lean.Analytic.V213.FiberOuterEndpointGuards
public import Erdos993Lean.Analytic.V213.FiberUniversalUpper

/-!
Exact Eq87 interpretation: factorial Taylor bounds give the strict
log/root start comparison. The actual clipped G and signed endpoint
budget are then bounded. The global target supremum is over all t>0 and
is exactly one, and the cutoff inequality is proved explicitly.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_wing_taylor_log {s tau p : ℝ} (hs : -1 < s) (hs0 : s ≤ 0)
    (htau : 0 < tau) (hp : 0 ≤ p)
    (hcheck : (1 + s) ^ 2 * fiberWingTaylor8 (2 * s) < tau ^ 5 * fiberWingTaylor4 (2 * p)) :
    s + Real.log (1 + s) < fiberEndpointLambda p tau := by
  have hsp : 0 < 1 + s := by linarith only [hs]
  have hu := fiber_wing_exp_negative_upper (z := -(2 * s)) (by linarith only [hs0])
  have hu' : Real.exp (2 * s) ≤ fiberWingTaylor8 (2 * s) := by simpa only [neg_neg] using hu
  have hl := fiber_wing_exp_positive_lower (x := 2 * p) (by linarith only [hp])
  have hexp : (1 + s) ^ 2 * Real.exp (2 * s) < tau ^ 5 * Real.exp (2 * p) :=
    (mul_le_mul_of_nonneg_left hu' (sq_nonneg (1 + s))).trans_lt
      (hcheck.trans_le (mul_le_mul_of_nonneg_left hl (by positivity)))
  have hlog := Real.log_lt_log (by positivity : 0 < (1 + s) ^ 2 * Real.exp (2 * s)) hexp
  simp (disch := positivity) only [Real.log_mul,Real.log_pow,Real.log_exp] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  unfold fiberEndpointLambda
  linarith only [hlog]

theorem fiber_wing_root_gain_strict {s lambda : ℝ} (hs : -1 < s) (hs0 : s < 0)
    (hl : s + Real.log (1 + s) < lambda) (hl0 : lambda < 0) :
    V22.G lambda < s ^ 2 / (1 + s) := by
  have he : rootMap (rootEquation s) = s := rootMap_eq_of_equation hs rfl
  have hsl : rootEquation s < lambda := hl
  have hsx : s < rootMap lambda := by
    have h := rootMap_strictMono hsl
    rw [he] at h
    exact h
  have hx : rootMap lambda < 0 := (rootMap_neg_iff lambda).2 hl0
  have hxp : 0 < 1 + rootMap lambda := by linarith only [rootMap_gt_neg_one lambda]
  have hsp : 0 < 1 + s := by linarith only [hs]
  have hsum : s + rootMap lambda + s * rootMap lambda < 0 := by
    have h := mul_neg_of_neg_of_pos hx hsp
    nlinarith only [h,hs0]
  have hprod := mul_pos_of_neg_of_neg (by linarith only [hsx] : s - rootMap lambda < 0) hsum
  rw [shared_G_eq]
  unfold rootG
  apply (div_lt_div_iff₀ hxp hsp).2
  nlinarith only [hprod]

theorem fiber_wing_constrained_root_bound {s lambda : ℝ} (hs : -1 < s) (hs0 : s < 0)
    (hl : s + Real.log (1 + s) < lambda) :
    V22.G (min 0 lambda) ≤ s ^ 2 / (1 + s) := by
  have hsp : 0 < 1 + s := by linarith only [hs]
  by_cases hneg : lambda < 0
  · rw [min_eq_right hneg.le]
    exact (fiber_wing_root_gain_strict hs hs0 hl hneg).le
  · have h0 : 0 ≤ lambda := le_of_not_gt hneg
    rw [min_eq_left h0,shared_G_zero]
    positivity

theorem fiber_wing_target_supremum :
    sSup ((fiberEndpointTarget 10 (9 / 2)) '' Ioi 0) = 1 := by
  have hn : ((fiberEndpointTarget 10 (9 / 2)) '' Ioi 0).Nonempty := ⟨_,1,by norm_num,rfl⟩
  have hb : BddAbove ((fiberEndpointTarget 10 (9 / 2)) '' Ioi 0) := by
    refine ⟨1,?_⟩
    rintro _ ⟨t,ht,rfl⟩
    exact fiber_upper_endpoint_cap ht
  apply le_antisymm
  · apply csSup_le hn
    rintro _ ⟨t,ht,rfl⟩
    exact fiber_upper_endpoint_cap ht
  · have h := le_csSup hb (show fiberEndpointTarget 10 (9 / 2) 1 ∈
        (fiberEndpointTarget 10 (9 / 2)) '' Ioi 0 from ⟨1,by norm_num,rfl⟩)
    norm_num [fiberEndpointTarget] at h
    exact h

theorem fiber_wing_endpoint_cutoff {p : ℝ} (hp : 0 ≤ p) :
    fiberEndpointStart p ^ 2 ≤ 2 * (9 / 2) / 9 := by
  rw [fiber_outer_endpoint_start_square]
  have he : Real.exp (-4 * p / 5) ≤ Real.exp 0 :=
    Real.exp_le_exp.mpr (by linarith only [hp])
  norm_num only [Real.exp_zero] at he ⊢
  exact he

theorem fiber_wing_endpoint_start (id : FiberWingIdentity) :
    max (fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau))
      (((lowMeanFractionReal (fiberWingById id).N0 - 2) /
        lowMeanFractionReal (fiberWingById id).N0) *
        fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau)) ≤
      fiberEndpointUpper (lowMeanFractionReal (fiberWingById id).p)
        (lowMeanFractionReal (fiberWingById id).d) (lowMeanFractionReal (fiberWingById id).R)
        (lowMeanFractionReal (fiberWingById id).tau) := by
  have hs := fiber_wing_guard_sound id .s0Min
  have hs0 := fiber_wing_guard_sound id .s0Max
  have ht := fiber_wing_guard_sound id .tauPos
  have hp := fiber_wing_guard_sound id .pPos
  have hR := fiber_wing_guard_sound id .RPos
  have hn := fiber_wing_guard_sound id .nMin
  change -1 < lowMeanFractionReal (fiberWingById id).s0 at hs
  change lowMeanFractionReal (fiberWingById id).s0 < 0 at hs0
  change 0 < lowMeanFractionReal (fiberWingById id).tau at ht
  change 0 < lowMeanFractionReal (fiberWingById id).p at hp
  change 0 < lowMeanFractionReal (fiberWingById id).R at hR
  change 13 ≤ lowMeanFractionReal (fiberWingById id).N0 at hn
  have hc := fiber_wing_taylor_checked id
  change (1 + lowMeanFractionReal (fiberWingById id).s0) ^ 2 *
    fiberWingTaylor8 (2 * lowMeanFractionReal (fiberWingById id).s0) <
    (lowMeanFractionReal (fiberWingById id).tau) ^ 5 *
      fiberWingTaylor4 (2 * lowMeanFractionReal (fiberWingById id).p) at hc
  have hl := fiber_wing_taylor_log hs hs0.le ht hp.le hc
  have hg := fiber_wing_constrained_root_bound hs hs0 hl
  have hloss := mul_le_mul_of_nonneg_left hg (by positivity :
    0 ≤ 2 / lowMeanFractionReal (fiberWingById id).R)
  have hgap := fiber_wing_gap_checked id
  change 1 / 100 < 1 + lowMeanFractionReal (fiberWingById id).d -
    2 * (lowMeanFractionReal (fiberWingById id).s0) ^ 2 /
      (lowMeanFractionReal (fiberWingById id).R * (1 + lowMeanFractionReal (fiberWingById id).s0)) -
    ((lowMeanFractionReal (fiberWingById id).N0 - 2) / lowMeanFractionReal (fiberWingById id).N0) *
      fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau) at hgap
  have hbudget :
    ((lowMeanFractionReal (fiberWingById id).N0 - 2) / lowMeanFractionReal (fiberWingById id).N0) *
      fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau) ≤
      fiberEndpointUpper (lowMeanFractionReal (fiberWingById id).p)
        (lowMeanFractionReal (fiberWingById id).d) (lowMeanFractionReal (fiberWingById id).R)
        (lowMeanFractionReal (fiberWingById id).tau) := by
    have he : 2 / lowMeanFractionReal (fiberWingById id).R *
        ((lowMeanFractionReal (fiberWingById id).s0) ^ 2 / (1 + lowMeanFractionReal (fiberWingById id).s0)) =
        2 * (lowMeanFractionReal (fiberWingById id).s0) ^ 2 /
          (lowMeanFractionReal (fiberWingById id).R * (1 + lowMeanFractionReal (fiberWingById id).s0)) := by
      simp only [div_eq_mul_inv,mul_inv_rev]
      ring
    rw [he] at hloss
    unfold fiberEndpointUpper
    linarith only [hgap,hloss]
  have hneg := fiber_wing_target_checked id
  change fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau) < 0 at hneg
  have heta : (lowMeanFractionReal (fiberWingById id).N0 - 2) /
      lowMeanFractionReal (fiberWingById id).N0 ≤ 1 :=
    (div_le_one (by linarith only [hn])).2 (by linarith)
  have hscaled : fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau) ≤
      ((lowMeanFractionReal (fiberWingById id).N0 - 2) / lowMeanFractionReal (fiberWingById id).N0) *
        fiberEndpointTarget 10 (9 / 2) (lowMeanFractionReal (fiberWingById id).tau) := by
    nlinarith only [heta,hneg.le]
  exact max_le (hscaled.trans hbudget) hbudget

end Erdos993Lean.Analytic.V213
