module

public import Erdos993Lean.Analytic.V213.FiberProfileControlRelations
public import Erdos993Lean.Analytic.V213.FiberProfileParameters

/-!
All twenty-four endpoint domains, checked by named printed identity.
Only Int/Nat cross-products are reduced. The five time caps are exactly
the printed profile domains; every root endpoint lies strictly below one.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberProfileTimeCapFraction : FiberRationalProfileIdentity → lowMeanFraction
  | .h => (19,50)
  | .g => (11,25)
  | .d => (13,25)
  | _ => (3,5)

theorem fiber_profile_time_cap_fraction (id : FiberRationalProfileIdentity) :
    lowMeanFractionValid (fiberProfileTimeCapFraction id) ∧
      lowMeanFractionReal (fiberProfileTimeCapFraction id) = fiberProfileTimeCap id := by
  cases id <;> norm_num [fiberProfileTimeCapFraction,fiberProfileTimeCap,
    lowMeanFractionReal,lowMeanFractionValid]

def fiberProfileControlCapDomain (t : lowMeanFraction) : Option FiberRationalProfileIdentity → Prop
  | none => True
  | some p => lowMeanFractionLE t (fiberProfileTimeCapFraction p)

instance fiberProfileControlCapDecidable (t : lowMeanFraction)
    (p : Option FiberRationalProfileIdentity) : Decidable (fiberProfileControlCapDomain t p) := by
  cases p <;> dsimp [fiberProfileControlCapDomain] <;> infer_instance

def fiberProfileControlMetadataCheck (id : FiberProfileControlIdentity) : Bool :=
  let r := fiberProfileControlById id
  decide (lowMeanFractionValid r.t ∧ lowMeanFractionValid r.a ∧
    lowMeanFractionLT (0,1) r.t ∧ lowMeanFractionLT r.a (1,1) ∧
    fiberProfileControlCapDomain r.t r.profile)

theorem fiber_profile_control_metadata_checks :
    (List.range 24).all (fun k => fiberProfileControlMetadataCheck (fiberProfileControlIdentityAt k)) = true := by
  decide +kernel

theorem fiber_profile_control_metadata_checked (id : FiberProfileControlIdentity) :
    fiberProfileControlMetadataCheck id = true := by
  have hk : fiberProfileControlIndex id < 24 := by cases id <;> decide +kernel
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_profile_control_metadata_checks
    (fiberProfileControlIndex id) hk
  have hb : fiberProfileControlIdentityAt (fiberProfileControlIndex id) = id := by cases id <;> rfl
  rwa [hb] at h

theorem fiber_profile_control_endpoint_domain (id : FiberProfileControlIdentity) :
    0 < lowMeanFractionReal (fiberProfileControlById id).t ∧
      lowMeanFractionReal (fiberProfileControlById id).a < 1 := by
  have h := of_decide_eq_true (fiber_profile_control_metadata_checked id)
  have hzero : lowMeanFractionValid (0,1) := by decide +kernel
  have hone : lowMeanFractionValid (1,1) := by decide +kernel
  constructor
  · have ht := (lowMean_fraction_lt_iff hzero h.1).mp h.2.2.1
    simpa [lowMeanFractionReal] using ht
  · have ha := (lowMean_fraction_lt_iff h.2.1 hone).mp h.2.2.2.1
    simpa [lowMeanFractionReal] using ha

theorem fiber_profile_control_time_cap (id : FiberProfileControlIdentity)
    (pid : FiberRationalProfileIdentity)
    (hp : (fiberProfileControlById id).profile = some pid) :
    lowMeanFractionReal (fiberProfileControlById id).t ≤ fiberProfileTimeCap pid := by
  have h := of_decide_eq_true (fiber_profile_control_metadata_checked id)
  have hc : lowMeanFractionLE (fiberProfileControlById id).t (fiberProfileTimeCapFraction pid) := by
    simpa only [hp,fiberProfileControlCapDomain] using h.2.2.2.2
  have hcap := fiber_profile_time_cap_fraction pid
  exact hcap.2 ▸ (lowMean_fraction_le_iff h.1 hcap.1).mp hc

end Erdos993Lean.Analytic.V213
