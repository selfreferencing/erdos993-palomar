module

public import Erdos993Lean.Analytic.V213.FiberProfileControlBounds

/-!
The seventeen printed E-to-profile cap comparisons, plus seven
identity cases for E itself. Every endpoint is the actual accepted F09
argument. The finite check also binds the full skew interval into E's
interval. Named identities, rather than list positions, govern use.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberProfileEControl : FiberProfileEndpointIdentity → FiberProfileControlIdentity
  | .third => .e_third
  | .p038 => .e_p038
  | .p042 => .e_p042
  | .p044 => .e_p044
  | .half => .e_half
  | .p052 => .e_p052
  | .p06 => .e_p06

def fiberProfileControlRelationCheck (id : FiberProfileControlIdentity) : Bool :=
  let r := fiberProfileControlById id
  let e := fiberProfileControlById (fiberProfileEControl r.endpoint)
  decide (r.t = fiberProfileEndpoint_t r.endpoint ∧
    r.a = fiberProfileEndpoint_a r.endpoint ∧
    e.t = r.t ∧ e.a = r.a ∧
    lowMeanFractionValid r.R ∧ lowMeanFractionValid e.R ∧
    lowMeanFractionValid r.z ∧ lowMeanFractionValid e.z ∧
    lowMeanFractionLE (0,1) r.R ∧ lowMeanFractionLE r.R e.R ∧
    lowMeanFractionLE e.z r.z)

theorem fiber_profile_control_relation_checks :
    (List.range 24).all (fun k => fiberProfileControlRelationCheck (fiberProfileControlIdentityAt k)) = true := by
  decide +kernel

theorem fiber_profile_control_relation_checked (id : FiberProfileControlIdentity) :
    fiberProfileControlRelationCheck id = true := by
  have hk : fiberProfileControlIndex id < 24 := by cases id <;> decide +kernel
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_profile_control_relation_checks
    (fiberProfileControlIndex id) hk
  have hb : fiberProfileControlIdentityAt (fiberProfileControlIndex id) = id := by cases id <;> rfl
  rwa [hb] at h

theorem fiber_profile_control_endpoint_binding (id : FiberProfileControlIdentity) :
    (fiberProfileControlById id).t = fiberProfileEndpoint_t (fiberProfileControlById id).endpoint ∧
      (fiberProfileControlById id).a = fiberProfileEndpoint_a (fiberProfileControlById id).endpoint := by
  have h := of_decide_eq_true (fiber_profile_control_relation_checked id)
  exact ⟨h.1,h.2.1⟩

theorem fiber_profile_E_control_identity (endpoint : FiberProfileEndpointIdentity) (u : ℝ) :
    fiberProfileControlEnvelope (fiberProfileEControl endpoint) u =
      fiberProfileE (lowMeanFractionReal (fiberProfileEndpoint_t endpoint)) u
        (lowMeanFractionReal (fiberProfileEndpoint_a endpoint)) := by
  cases endpoint <;> rfl

theorem fiber_profile_control_E_cap (id : FiberProfileControlIdentity) {u : ℝ}
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberProfileE (lowMeanFractionReal (fiberProfileControlById id).t) u
      (lowMeanFractionReal (fiberProfileControlById id).a) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have h := of_decide_eq_true (fiber_profile_control_relation_checked id)
  rcases h with ⟨ht,ha,het,hea,hR,heR,hz,hez,hR0,hRE,hEZ⟩
  have hREreal := (lowMean_fraction_le_iff hR heR).mp hRE
  have hEZreal := (lowMean_fraction_le_iff hez hz).mp hEZ
  have hbound := fiber_profile_control_endpoint_bound
    (fiberProfileEControl (fiberProfileControlById id).endpoint) hu (huR.trans hREreal)
  rw [fiber_profile_E_control_identity,← ht,← ha] at hbound
  exact hbound.trans_le hEZreal

end Erdos993Lean.Analytic.V213
