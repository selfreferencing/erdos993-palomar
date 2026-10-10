module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordShape

/-!
Grouped Int/Nat checks for all thirty-six complete F12 expressions.
Each accepted tree is compared to the actual F10/F11 formula shape.
Printed identity, dyadic domain, all scalar guards, epsilon and both
endpoint-route derivative guards are checked independently.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWeightedChordPrinted : FiberWeightedChordIdentity → String
  | .a_third_p042 => "F12:A:endpoints=1,3"
  | .a_p042_half => "F12:A:endpoints=3,5"
  | .a_half_p06 => "F12:A:endpoints=5,7"
  | .b_third_p042 => "F12:B:endpoints=1,3"
  | .b_p042_half => "F12:B:endpoints=3,5"
  | .b_half_p06 => "F12:B:endpoints=5,7"
  | .c_third_p042 => "F12:C:endpoints=1,3"
  | .c_p042_half => "F12:C:endpoints=3,5"
  | .c_half_p06 => "F12:C:endpoints=5,7"
  | .d_third_p042 => "F12:D:endpoints=1,3"
  | .d_p042_half => "F12:D:endpoints=3,5"
  | .d_half_p052 => "F12:D:endpoints=5,6"
  | .f_third_p042 => "F12:F:endpoints=1,3"
  | .f_p042_half => "F12:F:endpoints=3,5"
  | .f_half_p052 => "F12:F:endpoints=5,6"
  | .g_third_p042 => "F12:G:endpoints=1,3"
  | .g_p042_p044 => "F12:G:endpoints=3,4"
  | .h_third_p038 => "F12:H:endpoints=1,2"

def fiberWeightedChordExpectedN : FiberWeightedChordIdentity → ℕ
  | .a_third_p042 => 5
  | .a_p042_half => 4
  | .a_half_p06 => 2
  | .b_third_p042 => 4
  | .b_p042_half => 2
  | .b_half_p06 => 1
  | .c_third_p042 => 3
  | .c_p042_half => 1
  | .c_half_p06 => 0
  | .d_third_p042 => 2
  | .d_p042_half => 1
  | .d_half_p052 => 1
  | .f_third_p042 => 2
  | .f_p042_half => 1
  | .f_half_p052 => 0
  | .g_third_p042 => 1
  | .g_p042_p044 => 2
  | .h_third_p038 => 4

def fiberWeightedChordExpectedRoute : FiberWeightedChordIdentity → Bool
  | .g_p042_p044 | .h_third_p038 => true
  | _ => false

def fiberWeightedChordRoleAt : ℕ → FiberWeightedChordRole
  | 0 => .logarithm
  | _ => .gap

def fiberWeightedChordMetadata (id : FiberWeightedChordIdentity) : Prop :=
  let r := fiberWeightedChordById id
  let w := fiberWeightById r.weight
  let c := fiberProfileChordById r.chord
  let h := fiberProfileControlById c.right
  r.printed = fiberWeightedChordPrinted id ∧
  r.n = fiberWeightedChordExpectedN id ∧
  r.endpointRoute = fiberWeightedChordExpectedRoute id ∧
  c.profile = w.profile ∧
  w.chord_epsilon = some r.epsilon ∧
  lowMeanFractionValid r.s ∧ lowMeanFractionValid r.d ∧
  lowMeanFractionValid r.k ∧ lowMeanFractionValid r.v ∧
  lowMeanFractionValid r.y ∧ lowMeanFractionValid r.upper ∧
  lowMeanFractionValid r.gap ∧ lowMeanFractionValid r.epsilon ∧
  lowMeanFractionValid w.eta_w ∧
  lowMeanFractionLT (0,1) r.s ∧ lowMeanFractionLT (0,1) r.k ∧
  lowMeanFractionLT (0,1) w.eta_w ∧ lowMeanFractionLT (0,1) r.epsilon ∧
  lowMeanFractionLE ((2 : ℤ)^r.n,1) r.y ∧
  lowMeanFractionLT r.y ((2 : ℤ)^(r.n+1),1) ∧
  (r.endpointRoute = true → lowMeanFractionLE (1,1)
    (lowMeanFractionAdd (lowMeanFractionMul r.k h.z) (lowMeanFractionNeg r.s)))

instance fiberWeightedChordMetadataDecidable (id : FiberWeightedChordIdentity) :
    Decidable (fiberWeightedChordMetadata id) := by
  unfold fiberWeightedChordMetadata
  infer_instance

def fiberWeightedChordRelation (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole)
    (v : lowMeanFraction) : Prop :=
  let r := fiberWeightedChordById id
  match role with
  | .logarithm => lowMeanFractionEq v r.upper
  | .gap => lowMeanFractionEq v r.gap ∧ lowMeanFractionLE r.epsilon v

instance fiberWeightedChordRelationDecidable (id : FiberWeightedChordIdentity)
    (role : FiberWeightedChordRole) (v : lowMeanFraction) :
    Decidable (fiberWeightedChordRelation id role v) := by
  cases role <;> dsimp [fiberWeightedChordRelation] <;> infer_instance

def fiberWeightedChordRoleCheck (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) : Bool :=
  let e := fiberWeightedChordExpr id role
  lowMeanIntegerShapeCheck e (fiberWeightedChordShape id role) &&
    decide (fiberWeightedChordMetadata id ∧ fiberWeightedChordRelation id role (lowMeanIntegerExprValue e))

theorem fiber_weighted_chord_checks :
    (List.range 36).all (fun k => fiberWeightedChordRoleCheck
      (fiberWeightedChordIdentityAt (k/2)) (fiberWeightedChordRoleAt (k%2))) = true := by
  decide +kernel

theorem fiber_weighted_chord_index_checked {k : ℕ} (hk : k < 36) :
    fiberWeightedChordRoleCheck (fiberWeightedChordIdentityAt (k/2)) (fiberWeightedChordRoleAt (k%2)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_weighted_chord_checks k hk

theorem fiber_weighted_chord_named_checked (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) :
    fiberWeightedChordRoleCheck id role = true := by
  let k := fiberWeightedChordIndex id*2 + (match role with | .logarithm => 0 | .gap => 1)
  have hk : k < 36 := by cases id <;> cases role <;> decide +kernel
  have hi : fiberWeightedChordIdentityAt (k/2) = id ∧ fiberWeightedChordRoleAt (k%2) = role := by
    cases id <;> cases role <;> norm_num [k,fiberWeightedChordIndex,
      fiberWeightedChordIdentityAt,fiberWeightedChordRoleAt]
  have h := fiber_weighted_chord_index_checked hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_weighted_chord_metadata (id : FiberWeightedChordIdentity) :
    fiberWeightedChordMetadata id := by
  have h := fiber_weighted_chord_named_checked id .gap
  simp only [fiberWeightedChordRoleCheck,Bool.and_eq_true] at h
  exact (of_decide_eq_true h.2).1

theorem fiber_weighted_chord_shape_sound (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberWeightedChordExpr id role)) ∧
      fiberWeightedChordValue id role = lowMeanFractionReal (lowMeanIntegerExprValue (fiberWeightedChordExpr id role)) := by
  have h := fiber_weighted_chord_named_checked id role
  simp only [fiberWeightedChordRoleCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_weighted_chord_shape_real] at hs
  exact hs

theorem fiber_weighted_chord_log_value (id : FiberWeightedChordIdentity) :
    fiberWeightedChordValue id .logarithm = lowMeanFractionReal (fiberWeightedChordById id).upper := by
  have h := fiber_weighted_chord_named_checked id .logarithm
  simp only [fiberWeightedChordRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_weighted_chord_shape_sound id .logarithm
  have hm := hd.1
  simp only [fiberWeightedChordMetadata] at hm
  rw [hs.2]
  exact (lowMean_fraction_eq_iff hs.1 hm.2.2.2.2.2.2.2.2.2.2.1).mp hd.2

theorem fiber_weighted_chord_gap_value (id : FiberWeightedChordIdentity) :
    lowMeanFractionReal (fiberWeightedChordById id).epsilon ≤ fiberWeightedChordValue id .gap := by
  have h := fiber_weighted_chord_named_checked id .gap
  simp only [fiberWeightedChordRoleCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_weighted_chord_shape_sound id .gap
  have hm := hd.1
  simp only [fiberWeightedChordMetadata] at hm
  have hr := hd.2
  simp only [fiberWeightedChordRelation] at hr
  rw [hs.2]
  exact (lowMean_fraction_le_iff hm.2.2.2.2.2.2.2.2.2.2.2.2.1 hs.1).mp hr.2

end Erdos993Lean.Analytic.V213
