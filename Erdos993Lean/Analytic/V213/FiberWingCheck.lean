module

public import Erdos993Lean.Analytic.V213.FiberWingShape

/-!
Accepted F04 kernel checks: printed typed identities, all row leaves,
full canonical shapes and explicit Int/Nat comparisons. Range enumeration
only batches checks; named identities govern every theorem consumer.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWingParameters (r : FiberWingRow) : List lowMeanFraction :=
  [r.N0,r.R,r.a,r.b,r.d,r.eta,r.mu_W,r.p,r.s0,r.skew_lower,r.skew_upper,r.tau,
   r.sqrtUpper,r.gainCoefficient,r.taylorLeft,r.taylorRight,r.gap]

def fiberWingExpectedParameters : FiberWingIdentity → List lowMeanFraction
  | .w1 => [(13, 1), (22, 25), (7, 125), (3, 40), (3, 100), (11, 13), (19, 1), (11, 100), (-13, 25), (283, 5000), (741, 10000), (29, 50), (11, 3), (221, 100), (271824567898672, 3337860107421875), (3833756109466309, 46875000000000000), (15329, 248820)]
  | .w2 => [(13, 1), (17, 20), (37, 500), (9, 80), (13, 200), (11, 13), (20, 1), (7, 50), (-553, 1000), (37, 500), (139, 1250), (11, 20), (11, 3), (221, 100), (165284989713873635776332232223, 2500000000000000000000000000000), (1997708975251, 30000000000000), (4361, 395148)]
  | .w3 => [(31, 2), (41, 50), (11, 100), (17, 100), (7, 40), (27, 31), (26, 1), (9, 50), (-7, 12), (1111, 10000), (1667, 10000), (13, 25), (63, 16), (54, 25), (15063967235, 278628139008), (1663016520191, 30517578125000), (483179, 9913800)]

def fiberWingRelation (id : FiberWingIdentity) (role : FiberWingRole) (v : lowMeanFraction) : Prop :=
  let r := fiberWingById id
  match role with
  | .rate => lowMeanFractionValid r.R ∧ lowMeanFractionLE r.R v
  | .bonus => lowMeanFractionValid r.d ∧ lowMeanFractionLE r.d v
  | .gain => lowMeanFractionValid r.p ∧ lowMeanFractionLE r.p v
  | .rootSquare | .width => lowMeanFractionLE (0,1) v
  | .eta => lowMeanFractionValid r.eta ∧ lowMeanFractionEq v r.eta
  | .taylorLeft => lowMeanFractionValid r.taylorLeft ∧ lowMeanFractionEq v r.taylorLeft
  | .taylorRight => lowMeanFractionValid r.taylorRight ∧ lowMeanFractionEq v r.taylorRight ∧
      lowMeanFractionValid r.taylorLeft ∧ lowMeanFractionLT r.taylorLeft v
  | .gap => lowMeanFractionValid r.gap ∧ lowMeanFractionEq v r.gap ∧ lowMeanFractionLT (1,100) v
  | .target => lowMeanFractionLT v (0,1)

instance fiberWingRelationDecidable (id : FiberWingIdentity) (role : FiberWingRole) (v : lowMeanFraction) :
    Decidable (fiberWingRelation id role v) := by
  cases role <;> dsimp [fiberWingRelation] <;> infer_instance

def fiberWingCheck (id : FiberWingIdentity) (role : FiberWingRole) : Bool :=
  let r := fiberWingById id
  let e := fiberWingExpr id role
  lowMeanIntegerShapeCheck e (fiberWingShape id role) &&
    decide (r.printed = fiberWingPrinted id ∧ fiberWingParameters r = fiberWingExpectedParameters id ∧
      fiberWingRelation id role (lowMeanIntegerExprValue e))

theorem fiber_wing_checks :
    (List.range 30).all (fun k => fiberWingCheck (fiberWingIdentityAt (k / 10)) (fiberWingRoleAt (k % 10))) = true := by
  decide +kernel

theorem fiber_wing_index_checked {k : ℕ} (hk : k < 30) :
    fiberWingCheck (fiberWingIdentityAt (k / 10)) (fiberWingRoleAt (k % 10)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_wing_checks k hk

theorem fiber_wing_named_checked (id : FiberWingIdentity) (role : FiberWingRole) :
    fiberWingCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

theorem fiber_wing_shape_sound (id : FiberWingIdentity) (role : FiberWingRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberWingExpr id role)) ∧
      fiberWingValue id role = lowMeanFractionReal (lowMeanIntegerExprValue (fiberWingExpr id role)) := by
  have h := fiber_wing_named_checked id role
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_wing_shape_real] at hs
  exact hs

theorem fiber_wing_rate_checked (id : FiberWingIdentity) :
    lowMeanFractionReal (fiberWingById id).R ≤ fiberWingValue id .rate := by
  have h := fiber_wing_named_checked id .rate
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .rate
  rw [hs.2]
  exact (lowMean_fraction_le_iff hd.2.2.1 hs.1).mp hd.2.2.2

theorem fiber_wing_bonus_checked (id : FiberWingIdentity) :
    lowMeanFractionReal (fiberWingById id).d ≤ fiberWingValue id .bonus := by
  have h := fiber_wing_named_checked id .bonus
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .bonus
  rw [hs.2]
  exact (lowMean_fraction_le_iff hd.2.2.1 hs.1).mp hd.2.2.2

theorem fiber_wing_gain_checked (id : FiberWingIdentity) :
    lowMeanFractionReal (fiberWingById id).p ≤ fiberWingValue id .gain := by
  have h := fiber_wing_named_checked id .gain
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .gain
  rw [hs.2]
  exact (lowMean_fraction_le_iff hd.2.2.1 hs.1).mp hd.2.2.2

theorem fiber_wing_rootSquare_checked (id : FiberWingIdentity) : 0 ≤ fiberWingValue id .rootSquare := by
  have h := fiber_wing_named_checked id .rootSquare
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .rootSquare
  rw [hs.2]
  have hc := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (0,1)) hs.1).mp hd.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

theorem fiber_wing_width_checked (id : FiberWingIdentity) : 0 ≤ fiberWingValue id .width := by
  have h := fiber_wing_named_checked id .width
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .width
  rw [hs.2]
  have hc := (lowMean_fraction_le_iff (by decide +kernel : lowMeanFractionValid (0,1)) hs.1).mp hd.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

theorem fiber_wing_taylor_checked (id : FiberWingIdentity) :
    fiberWingValue id .taylorLeft < fiberWingValue id .taylorRight := by
  have h := fiber_wing_named_checked id .taylorRight
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hl := fiber_wing_named_checked id .taylorLeft
  simp only [fiberWingCheck,Bool.and_eq_true] at hl
  have hld := of_decide_eq_true hl.2
  simp only [fiberWingRelation] at hld
  have sl := fiber_wing_shape_sound id .taylorLeft
  have sr := fiber_wing_shape_sound id .taylorRight
  rw [sl.2,sr.2]
  have he := (lowMean_fraction_eq_iff sl.1 hld.2.2.1).mp hld.2.2.2
  rw [he]
  exact (lowMean_fraction_lt_iff hd.2.2.2.2.1 sr.1).mp hd.2.2.2.2.2

theorem fiber_wing_gap_checked (id : FiberWingIdentity) :
    1 / 100 < fiberWingValue id .gap := by
  have h := fiber_wing_named_checked id .gap
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .gap
  rw [hs.2]
  have hc := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (1,100)) hs.1).mp hd.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_one,Nat.cast_ofNat] using hc

theorem fiber_wing_eta_checked (id : FiberWingIdentity) :
    fiberWingValue id .eta = lowMeanFractionReal (fiberWingById id).eta := by
  have h := fiber_wing_named_checked id .eta
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .eta
  rw [hs.2]
  exact (lowMean_fraction_eq_iff hs.1 hd.2.2.1).mp hd.2.2.2

theorem fiber_wing_target_checked (id : FiberWingIdentity) : fiberWingValue id .target < 0 := by
  have h := fiber_wing_named_checked id .target
  simp only [fiberWingCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberWingRelation] at hd
  have hs := fiber_wing_shape_sound id .target
  rw [hs.2]
  have hc := (lowMean_fraction_lt_iff hs.1 (by decide +kernel : lowMeanFractionValid (0,1))).mp hd.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

end Erdos993Lean.Analytic.V213
