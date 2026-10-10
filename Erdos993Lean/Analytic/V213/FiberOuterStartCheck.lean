module

public import Erdos993Lean.Analytic.V213.FiberOuterStartShape

/-!
Accepted F05 starts: grouped Int/Nat kernel checking and real
soundness. Each entire expression is compared with the canonical formula
including every leaf. Printed identities and all start parameters are
checked separately. Range indices enumerate, but never identify, rows.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberOuterStartParameters (r : FiberOuterStartRow) : List lowMeanFraction :=
  [r.n,r.a,r.sigma,r.b0,r.beta0,r.d_star,r.p_star,r.R_star,r.v_star,r.logUpper]

def fiberOuterExpectedParameters : FiberOuterStartIdentity → List lowMeanFraction
  | .c3 => [(24,1),(4,25),(11,25),(0,1),(1,2),(3,5),(3,10),(2,3),(107,60),(5,6)]
  | .c4 => [(18,1),(9,40),(21,50),(3,20),(3,10),(9,10),(2,5),(2,3),(143,80),(7,8)]
  | .c5c6 => [(20,1),(4,15),(9,25),(3,10),(0,1),(29,20),(11,20),(3,4),(161,80),(41,40)]
  | .c7c8 => [(17,1),(17,50),(3,10),(3,10),(1,1),(2,1),(13,20),(2,3),(19,8),(121,100)]

def fiberOuterStartRelation (id : FiberOuterStartIdentity) (role : FiberOuterStartRole)
    (v : lowMeanFraction) : Prop :=
  let r := fiberOuterStartById id
  match role with
      | .gain => lowMeanFractionValid r.P ∧ lowMeanFractionEq v r.P ∧
          lowMeanFractionValid r.p_star ∧ lowMeanFractionLT r.p_star v
      | .rate => lowMeanFractionValid r.R ∧ lowMeanFractionEq v r.R ∧
          lowMeanFractionValid r.R_star ∧ lowMeanFractionLE r.R_star v
      | .bonus => lowMeanFractionValid r.delta ∧ lowMeanFractionEq v r.delta ∧
          lowMeanFractionValid r.d_star ∧ lowMeanFractionLE r.d_star v
      | .logarithm => lowMeanFractionValid r.logUpper ∧ lowMeanFractionLE v r.logUpper
      | .target => lowMeanFractionValid r.f0 ∧ lowMeanFractionEq v r.f0 ∧ lowMeanFractionLT v (0,1)
      | .gap => lowMeanFractionValid r.printed_gap ∧ lowMeanFractionEq v r.printed_gap ∧
          lowMeanFractionLT (1,40) v

instance fiberOuterStartRelationDecidable (id : FiberOuterStartIdentity) (role : FiberOuterStartRole)
    (v : lowMeanFraction) : Decidable (fiberOuterStartRelation id role v) := by
  cases role <;> dsimp [fiberOuterStartRelation] <;> infer_instance

def fiberOuterStartRoleCheck (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) : Bool :=
  let r := fiberOuterStartById id
  let e := fiberOuterStartExpr id role
  let v := lowMeanIntegerExprValue e
  lowMeanIntegerShapeCheck e (fiberOuterStartShape id role) &&
    decide (r.printed = fiberOuterStartPrinted id ∧
      fiberOuterStartParameters r = fiberOuterExpectedParameters id ∧ fiberOuterStartRelation id role v)

theorem fiber_outer_start_checks :
    (List.range 24).all (fun k => fiberOuterStartRoleCheck
      (fiberOuterStartIdentityAt (k / 6)) (fiberOuterStartRoleAt (k % 6))) = true := by
  decide +kernel

theorem fiber_outer_start_index_checked {k : ℕ} (hk : k < 24) :
    fiberOuterStartRoleCheck (fiberOuterStartIdentityAt (k / 6)) (fiberOuterStartRoleAt (k % 6)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_outer_start_checks k hk

theorem fiber_outer_named_start_checked (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) :
    fiberOuterStartRoleCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

theorem fiber_outer_start_shape_sound (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberOuterStartExpr id role)) ∧
      fiberOuterStartValue id role =
        lowMeanFractionReal (lowMeanIntegerExprValue (fiberOuterStartExpr id role)) := by
  have h := fiber_outer_named_start_checked id role
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_outer_start_shape_real] at hs
  exact hs

theorem fiber_outer_start_gain (id : FiberOuterStartIdentity) :
    lowMeanFractionReal (fiberOuterStartById id).p_star < fiberOuterStartValue id .gain := by
  have h := fiber_outer_named_start_checked id .gain
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .gain
  rw [hs.2]
  exact (lowMean_fraction_lt_iff hd.2.2.2.2.1 hs.1).mp hd.2.2.2.2.2

theorem fiber_outer_start_rate (id : FiberOuterStartIdentity) :
    lowMeanFractionReal (fiberOuterStartById id).R_star ≤ fiberOuterStartValue id .rate := by
  have h := fiber_outer_named_start_checked id .rate
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .rate
  rw [hs.2]
  exact (lowMean_fraction_le_iff hd.2.2.2.2.1 hs.1).mp hd.2.2.2.2.2

theorem fiber_outer_start_bonus (id : FiberOuterStartIdentity) :
    lowMeanFractionReal (fiberOuterStartById id).d_star ≤ fiberOuterStartValue id .bonus := by
  have h := fiber_outer_named_start_checked id .bonus
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .bonus
  rw [hs.2]
  exact (lowMean_fraction_le_iff hd.2.2.2.2.1 hs.1).mp hd.2.2.2.2.2

theorem fiber_outer_start_log (id : FiberOuterStartIdentity) :
    fiberOuterStartValue id .logarithm ≤ lowMeanFractionReal (fiberOuterStartById id).logUpper := by
  have h := fiber_outer_named_start_checked id .logarithm
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .logarithm
  rw [hs.2]
  exact (lowMean_fraction_le_iff hs.1 hd.2.2.1).mp hd.2.2.2

theorem fiber_outer_start_target (id : FiberOuterStartIdentity) :
    fiberOuterStartValue id .target = lowMeanFractionReal (fiberOuterStartById id).f0 ∧
      fiberOuterStartValue id .target < 0 := by
  have h := fiber_outer_named_start_checked id .target
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .target
  rw [hs.2]
  refine ⟨(lowMean_fraction_eq_iff hs.1 hd.2.2.1).mp hd.2.2.2.1, ?_⟩
  have hc := (lowMean_fraction_lt_iff hs.1 (by decide +kernel : lowMeanFractionValid (0,1))).mp hd.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

theorem fiber_outer_start_gap (id : FiberOuterStartIdentity) :
    fiberOuterStartValue id .gap = lowMeanFractionReal (fiberOuterStartById id).printed_gap ∧
      1 / 40 < fiberOuterStartValue id .gap := by
  have h := fiber_outer_named_start_checked id .gap
  simp only [fiberOuterStartRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberOuterStartRelation] at hd
  have hs := fiber_outer_start_shape_sound id .gap
  rw [hs.2]
  refine ⟨(lowMean_fraction_eq_iff hs.1 hd.2.2.1).mp hd.2.2.2.1, ?_⟩
  have hc := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (1,40)) hs.1).mp hd.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_one,Nat.cast_ofNat] using hc

end Erdos993Lean.Analytic.V213
