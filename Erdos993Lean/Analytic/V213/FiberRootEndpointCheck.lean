module

public import Erdos993Lean.Analytic.V213.FiberRootLineGeometry

/-!
All seven printed endpoint arguments and every root-line piece
containing them. All 21 possible named associations are enumerated;
the nine in-piece associations satisfy the literal rational line
containment. Actual root bounds then follow from the closed-piece
geometry.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

def fiberRootEndpointLineFraction (id : FiberRootLineIdentity)
    (endpoint : FiberProfileEndpointIdentity) : lowMeanFraction :=
  lowMeanFractionAdd (fiberRootLineById id).alpha
    (lowMeanFractionNeg (lowMeanFractionMul (fiberRootLineById id).beta (fiberProfileEndpoint_t endpoint)))

def fiberRootEndpointCheck (id : FiberRootLineIdentity) (endpoint : FiberProfileEndpointIdentity) : Bool :=
  let r := fiberRootLineById id
  let t := fiberProfileEndpoint_t endpoint
  let a := fiberProfileEndpoint_a endpoint
  let line := fiberRootEndpointLineFraction id endpoint
  decide (lowMeanFractionValid r.lo ∧ lowMeanFractionValid r.hi ∧
    lowMeanFractionValid r.alpha ∧ lowMeanFractionValid r.beta ∧
    lowMeanFractionValid t ∧ lowMeanFractionValid a ∧ lowMeanFractionValid line ∧
    ((lowMeanFractionLE r.lo t ∧ lowMeanFractionLE t r.hi) → lowMeanFractionLE line a))

theorem fiber_root_endpoint_checks :
    (List.range 21).all (fun k => fiberRootEndpointCheck (fiberRootLineIdentityAt (k / 7))
      (fiberProfileEndpointIdentityAt (k % 7))) = true := by
  decide +kernel

theorem fiber_root_endpoint_index_checked {k : ℕ} (hk : k < 21) :
    fiberRootEndpointCheck (fiberRootLineIdentityAt (k / 7)) (fiberProfileEndpointIdentityAt (k % 7)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_root_endpoint_checks k hk

theorem fiber_root_endpoint_named_checked (id : FiberRootLineIdentity) (endpoint : FiberProfileEndpointIdentity) :
    fiberRootEndpointCheck id endpoint = true := by
  cases id <;> cases endpoint <;> decide +kernel

theorem fiber_root_endpoint_containment (id : FiberRootLineIdentity) (endpoint : FiberProfileEndpointIdentity)
    (ht : lowMeanFractionReal (fiberProfileEndpoint_t endpoint) ∈
      Icc (lowMeanFractionReal (fiberRootLineById id).lo) (lowMeanFractionReal (fiberRootLineById id).hi)) :
    lowMeanFractionReal (fiberRootLineById id).alpha -
      lowMeanFractionReal (fiberRootLineById id).beta * lowMeanFractionReal (fiberProfileEndpoint_t endpoint) ≤
        lowMeanFractionReal (fiberProfileEndpoint_a endpoint) := by
  have hd := of_decide_eq_true (fiber_root_endpoint_named_checked id endpoint)
  change lowMeanFractionValid (fiberRootLineById id).lo ∧ _ at hd
  rcases hd with ⟨hlo,hhi,halpha,hbeta,hpt,hpa,hline,himp⟩
  have hmembership := And.intro ((lowMean_fraction_le_iff hlo hpt).mpr ht.1)
    ((lowMean_fraction_le_iff hpt hhi).mpr ht.2)
  have hc := (lowMean_fraction_le_iff hline hpa).mp (himp hmembership)
  have hid : lowMeanFractionReal (fiberRootEndpointLineFraction id endpoint) =
      lowMeanFractionReal (fiberRootLineById id).alpha -
        lowMeanFractionReal (fiberRootLineById id).beta * lowMeanFractionReal (fiberProfileEndpoint_t endpoint) := by
    unfold fiberRootEndpointLineFraction
    rw [lowMean_fraction_add halpha (show lowMeanFractionValid
      (lowMeanFractionNeg (lowMeanFractionMul (fiberRootLineById id).beta (fiberProfileEndpoint_t endpoint)))
        from Nat.mul_pos hbeta hpt),lowMean_fraction_neg,lowMean_fraction_mul]
    ring
  rwa [hid] at hc

def fiberRootEndpointPiece : FiberProfileEndpointIdentity → FiberRootLineIdentity
  | .third | .p038 | .p042 => .third_042
  | .p044 | .half => .p042_half
  | .p052 | .p06 => .half_p06

theorem fiber_root_endpoint_piece (endpoint : FiberProfileEndpointIdentity) :
    lowMeanFractionReal (fiberProfileEndpoint_t endpoint) ∈
      Icc (lowMeanFractionReal (fiberRootLineById (fiberRootEndpointPiece endpoint)).lo)
        (lowMeanFractionReal (fiberRootLineById (fiberRootEndpointPiece endpoint)).hi) := by
  cases endpoint <;> norm_num [fiberRootEndpointPiece,fiberRootLineById,fiberProfileEndpoint_t,lowMeanFractionReal]

theorem fiber_root_endpoint_actual (endpoint : FiberProfileEndpointIdentity) :
    fiberRayAroot (lowMeanFractionReal (fiberProfileEndpoint_t endpoint)) <
      lowMeanFractionReal (fiberProfileEndpoint_a endpoint) := by
  have hm := fiber_root_endpoint_piece endpoint
  exact (fiber_root_line_bound (fiberRootEndpointPiece endpoint) hm).trans_le
    (fiber_root_endpoint_containment (fiberRootEndpointPiece endpoint) endpoint hm)

end Erdos993Lean.Analytic.V213
