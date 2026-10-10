module

public import Erdos993Lean.Analytic.V213.FiberInputRateCheck
public import Erdos993Lean.Analytic.V213.FiberIntervalSkew

/-!
All55 actual accepted N44 closed input intervals. The checks
use only signed numerator/natural-denominator comparisons, after reading
actual endpoint fractions. The activity/probability map and the complete
absolute-skew interval bound are proved for every real activity.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberInputQloFraction (id : FiberInputIdentity) : lowMeanFraction :=
  lowMeanActivityQFraction (fiberInputLoFraction id)

def fiberInputQhiFraction (id : FiberInputIdentity) : lowMeanFraction :=
  lowMeanActivityQFraction (fiberInputHiFraction id)

def fiberInputSignedSkewFraction (x : lowMeanFraction) : lowMeanFraction :=
  fiberFractionSub (lowMeanFractionMul (2,1) x) (1,1)

def fiberInputDomainTests (id : FiberInputIdentity) : Prop :=
  lowMeanFractionValid (fiberInputLoFraction id) ∧
  lowMeanFractionValid (fiberInputHiFraction id) ∧
  lowMeanFractionValid (fiberInputQloFraction id) ∧
  lowMeanFractionValid (fiberInputQhiFraction id) ∧
  0 ≤ (fiberInputLoFraction id).1 ∧ 0 ≤ (fiberInputHiFraction id).1 ∧
  lowMeanFractionLE (fiberInputLoFraction id) (fiberInputHiFraction id) ∧
  lowMeanFractionLE (1,3) (fiberInputLoFraction id) ∧
  lowMeanFractionLE (fiberInputHiFraction id) (7,3) ∧
  lowMeanFractionLE (1,4) (fiberInputQloFraction id) ∧
  lowMeanFractionLE (fiberInputQhiFraction id) (3,4) ∧
  (fiberInputRouteById id).printed = fiberInputPrinted id ∧
  (fiberInputRouteById id).iota = fiberInputIndex id ∧
  lowMeanFractionValid (fiberInputRouteById id).mu0 ∧
  lowMeanFractionLT (0,1) (fiberInputRouteById id).mu0

instance fiberInputDomainTestsDecidable (id : FiberInputIdentity) :
    Decidable (fiberInputDomainTests id) := by
  unfold fiberInputDomainTests
  infer_instance

theorem fiber_input_domain_checks :
    (List.range 55).all (fun k => decide (fiberInputDomainTests (fiberInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_input_domain_facts (id : FiberInputIdentity) : fiberInputDomainTests id := by
  have hk : fiberInputIndex id < 55 := by cases id <;> decide +kernel
  have hi : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_input_domain_checks (fiberInputIndex id) hk
  rw [hi] at h
  exact of_decide_eq_true h

theorem fiber_activity_q_monotone {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    FreeCountVariance.q x ≤ FreeCountVariance.q y := by
  have hy := hx.trans hxy
  unfold FreeCountVariance.q
  apply (div_le_div_iff₀ (by linarith only [hx]) (by linarith only [hy])).2
  nlinarith only [hxy]

theorem fiber_input_qlo_real (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputQloFraction id) = FreeCountVariance.q (lowMeanFractionReal (fiberInputLoFraction id)) := by
  have h := fiber_input_domain_facts id
  exact lowMean_activityQ_fraction h.1 h.2.2.2.2.1

theorem fiber_input_qhi_real (id : FiberInputIdentity) :
    lowMeanFractionReal (fiberInputQhiFraction id) = FreeCountVariance.q (lowMeanFractionReal (fiberInputHiFraction id)) := by
  have h := fiber_input_domain_facts id
  exact lowMean_activityQ_fraction h.2.1 h.2.2.2.2.2.1

theorem fiber_input_activity_nonneg (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda) : 0 ≤ lambda := by
  have h := fiber_input_domain_facts id
  have hlo : 0 ≤ lowMeanFractionReal (fiberInputLoFraction id) := by
    unfold lowMeanFractionReal
    exact div_nonneg (by exact_mod_cast h.2.2.2.2.1) (Nat.cast_nonneg _)
  exact hlo.trans hl

theorem fiber_input_q_interval (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    FreeCountVariance.q lambda ∈ Set.Icc (lowMeanFractionReal (fiberInputQloFraction id))
      (lowMeanFractionReal (fiberInputQhiFraction id)) := by
  have h := fiber_input_domain_facts id
  have hlo := fiber_input_activity_nonneg id (le_refl _)
  have hlam := fiber_input_activity_nonneg id hl
  rw [fiber_input_qlo_real,fiber_input_qhi_real]
  exact ⟨fiber_activity_q_monotone hlo hl,fiber_activity_q_monotone hlam hh⟩

theorem fiber_input_probability_domain (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    FreeCountVariance.q lambda ∈ Set.Icc (1/4) (3/4) := by
  have h := fiber_input_domain_facts id
  have hq := fiber_input_q_interval id hl hh
  have hlq := (lowMean_fraction_le_iff (by norm_num [lowMeanFractionValid]) h.2.2.1).mp
    h.2.2.2.2.2.2.2.2.2.1
  have hhq := (lowMean_fraction_le_iff h.2.2.2.1 (by norm_num [lowMeanFractionValid])).mp
    h.2.2.2.2.2.2.2.2.2.2.1
  norm_num [lowMeanFractionReal] at hlq hhq
  exact ⟨hlq.trans hq.1,hq.2.trans hhq⟩

theorem fiber_input_signed_skew_real {x : lowMeanFraction} (hx : lowMeanFractionValid x) :
    lowMeanFractionReal (fiberInputSignedSkewFraction x) = fiberSkew (lowMeanFractionReal x) := by
  have hm : lowMeanFractionValid (lowMeanFractionMul (2,1) x) :=
    Nat.mul_pos (by norm_num [lowMeanFractionValid]) hx
  rw [fiberInputSignedSkewFraction,fiber_fraction_sub_real hm (by norm_num [lowMeanFractionValid]),lowMean_fraction_mul]
  norm_num [lowMeanFractionReal,fiberSkew]

theorem fiber_input_whole_skew (id : FiberInputIdentity) {lambda : ℝ}
    (hl : lowMeanFractionReal (fiberInputLoFraction id) ≤ lambda)
    (hh : lambda ≤ lowMeanFractionReal (fiberInputHiFraction id)) :
    |fiberSkew (FreeCountVariance.q lambda)| ≤
      fiberInputSkewHigh (lowMeanFractionReal (fiberInputQloFraction id))
        (lowMeanFractionReal (fiberInputQhiFraction id)) :=
  fiber_skew_interval_bound (fiber_input_q_interval id hl hh)

theorem fiber_input_starting_mean_positive (id : FiberInputIdentity) :
    0 < lowMeanFractionReal (fiberInputRouteById id).mu0 := by
  have h := fiber_input_domain_facts id
  have hv := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hp := (lowMean_fraction_lt_iff (by norm_num [lowMeanFractionValid]) hv).mp
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hp

end Erdos993Lean.Analytic.V213
