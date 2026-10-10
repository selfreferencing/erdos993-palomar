module

public import Erdos993Lean.Analytic.V213.FiberWindowShape

/-!
Grouped whole-number checks for all eighty complete F13 window trees.
Printed identity/class/parameters, each formula result, strict positive
X-gap and exact signed-price value are checked before real consumers.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

instance fiberWindowOuterClassDecidableEq : DecidableEq FiberOuterClassIdentity := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

def fiberWindowPrintedParameters (r : FiberWindowRow) : List lowMeanFraction :=
  [r.l,r.h,r.N0,r.v,r.X,r.epsilon_X,r.L_W]

def fiberWindowExpectedParameters : FiberWindowIdentity → List lowMeanFraction
  | .window1 => [(13, 25), (3, 5), (127, 5), (3, 4), (1, 1), (1, 1), (0, 1)]
  | .window2 => [(27, 50), (69, 100), (29, 1), (3, 4), (1, 1), (1, 10), (2351, 20000)]
  | .window3 => [(19, 50), (2, 5), (86, 5), (3, 5), (-7, 2), (1, 100), (127, 380)]
  | .window4 => [(2, 5), (21, 50), (18, 1), (3, 5), (-5, 2), (1, 100), (1269, 20000)]
  | .window5 => [(17, 50), (2, 5), (19, 1), (3, 5), (-17, 4), (1, 100), (49, 50)]
  | .window6 => [(3, 10), (33, 100), (17, 1), (3, 5), (-38, 5), (1, 100), (29047, 20000)]
  | .window7 => [(33, 100), (9, 25), (37, 2), (3, 5), (-33, 8), (1, 100), (2409, 5000)]
  | .window8 => [(1, 4), (3, 10), (29, 2), (1, 2), (-18, 1), (1, 10), (3959, 1000)]
  | .window9 => [(3, 10), (33, 100), (17, 1), (1, 2), (-15, 2), (1, 10), (14899, 20000)]
  | .window10 => [(1, 4), (3, 10), (29, 2), (1, 2), (-16, 1), (1, 10), (3263, 1000)]

def fiberWindowExpectedClass : FiberWindowIdentity → FiberOuterClassIdentity
  | .window1 => .c1
  | .window2 => .c2
  | .window3 => .c4
  | .window4 => .c4
  | .window5 => .c5
  | .window6 => .c6
  | .window7 => .c6
  | .window8 => .c7
  | .window9 => .c7
  | .window10 => .c8

def fiberWindowExpectedValue (id : FiberWindowIdentity) (role : FiberWindowRole) : lowMeanFraction :=
  let r := fiberWindowById id
  match role with
  | .gain => r.phi
  | .rate => r.rho0
  | .bonus => r.Delta0
  | .anchor => r.x
  | .inverse => r.w
  | .minorant => r.actual_X
  | .gap => lowMeanFractionAdd r.actual_X (lowMeanFractionNeg r.X)
  | .price => r.L_W

def fiberWindowMetadata (id : FiberWindowIdentity) : Prop :=
  let r := fiberWindowById id
  r.printed = fiberWindowPrinted id ∧
  r.outerClass = fiberWindowExpectedClass id ∧
  fiberWindowPrintedParameters r = fiberWindowExpectedParameters id ∧
  r.a = (fiberOuterClassById r.outerClass).skew_lower ∧
  r.b = (fiberOuterClassById r.outerClass).skew_upper ∧
  lowMeanFractionValid r.epsilon_X ∧ lowMeanFractionLT (0,1) r.epsilon_X

instance fiberWindowMetadataDecidable (id : FiberWindowIdentity) : Decidable (fiberWindowMetadata id) := by
  unfold fiberWindowMetadata
  infer_instance

def fiberWindowRelation (id : FiberWindowIdentity) (role : FiberWindowRole) (v : lowMeanFraction) : Prop :=
  lowMeanFractionValid (fiberWindowExpectedValue id role) ∧
  lowMeanFractionEq v (fiberWindowExpectedValue id role) ∧
    (role = .gap → lowMeanFractionLE (fiberWindowById id).epsilon_X v)

instance fiberWindowRoleDecidableEq : DecidableEq FiberWindowRole := by
  intro a b
  cases a <;> cases b <;> first | exact isTrue rfl | exact isFalse (by intro h; cases h)

instance fiberWindowRelationDecidable (id : FiberWindowIdentity) (role : FiberWindowRole)
    (v : lowMeanFraction) : Decidable (fiberWindowRelation id role v) := by
  unfold fiberWindowRelation
  infer_instance

def fiberWindowCheck (id : FiberWindowIdentity) (role : FiberWindowRole) : Bool :=
  let e := fiberWindowExpr id role
  lowMeanIntegerShapeCheck e (fiberWindowShape id role) &&
    decide (fiberWindowMetadata id ∧ fiberWindowRelation id role (lowMeanIntegerExprValue e))

theorem fiber_window_checks :
    (List.range 80).all (fun k => fiberWindowCheck
      (fiberWindowIdentityAt (k/8)) (fiberWindowRoleAt (k%8))) = true := by
  decide +kernel

theorem fiber_window_index_checked {k : ℕ} (hk : k < 80) :
    fiberWindowCheck (fiberWindowIdentityAt (k/8)) (fiberWindowRoleAt (k%8)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_window_checks k hk

theorem fiber_window_named_checked (id : FiberWindowIdentity) (role : FiberWindowRole) :
    fiberWindowCheck id role = true := by
  let k := fiberWindowIndex id*8 + (match role with
    | .gain => 0 | .rate => 1 | .bonus => 2 | .anchor => 3
    | .inverse => 4 | .minorant => 5 | .gap => 6 | .price => 7)
  have hk : k < 80 := by cases id <;> cases role <;> decide +kernel
  have hi : fiberWindowIdentityAt (k/8) = id ∧ fiberWindowRoleAt (k%8) = role := by
    cases id <;> cases role <;> norm_num [k,fiberWindowIndex,fiberWindowIdentityAt,fiberWindowRoleAt]
  have h := fiber_window_index_checked hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_window_metadata (id : FiberWindowIdentity) : fiberWindowMetadata id := by
  have h := fiber_window_named_checked id .gap
  simp only [fiberWindowCheck,Bool.and_eq_true] at h
  exact (of_decide_eq_true h.2).1

theorem fiber_window_shape_sound (id : FiberWindowIdentity) (role : FiberWindowRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberWindowExpr id role)) ∧
      fiberWindowValue id role = lowMeanFractionReal (lowMeanIntegerExprValue (fiberWindowExpr id role)) := by
  have h := fiber_window_named_checked id role
  simp only [fiberWindowCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_window_shape_real] at hs
  exact hs

theorem fiber_window_value_checked (id : FiberWindowIdentity) (role : FiberWindowRole) :
    fiberWindowValue id role = lowMeanFractionReal (fiberWindowExpectedValue id role) := by
  have h := fiber_window_named_checked id role
  simp only [fiberWindowCheck,Bool.and_eq_true] at h
  have hd := (of_decide_eq_true h.2).2
  have hs := fiber_window_shape_sound id role
  rw [hs.2]
  exact (lowMean_fraction_eq_iff hs.1 hd.1).mp hd.2.1

theorem fiber_window_gap_checked (id : FiberWindowIdentity) :
    lowMeanFractionReal (fiberWindowById id).epsilon_X ≤ fiberWindowValue id .gap := by
  have h := fiber_window_named_checked id .gap
  simp only [fiberWindowCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_window_shape_sound id .gap
  have heps := hd.1.2.2.2.2.2.1
  rw [hs.2]
  exact (lowMean_fraction_le_iff heps hs.1).mp (hd.2.2.2 rfl)

theorem fiber_window_epsilon_positive (id : FiberWindowIdentity) :
    0 < lowMeanFractionReal (fiberWindowById id).epsilon_X := by
  have h := fiber_window_metadata id
  have hp := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1))
    h.2.2.2.2.2.1).mp h.2.2.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,zero_div] using hp

end Erdos993Lean.Analytic.V213
