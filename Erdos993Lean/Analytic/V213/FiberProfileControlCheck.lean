module

public import Erdos993Lean.Analytic.V213.FiberProfileControlShape

/-!
Accepted F10 canonical coefficient/E/V checks. Typed printed
identities govern every consumer; Range.all only batches the checks.
Every operation/leaf is bound to the actual Eq94/95 coefficient formulas
before the Int/Nat comparison is interpreted in the reals.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberProfileControlParameters (r : FiberProfileControlRow) : List lowMeanFraction :=
  [r.t,r.a,r.R,r.z,r.e1,r.e2]

def fiberProfileControlExpectedParameters : FiberProfileControlIdentity → List lowMeanFraction
  | .a_third => [(1,3), (8527,10000), (1,4), (33,10), (1,1), (1,1000)]
  | .a_p042 => [(21,50), (7583,10000), (1,4), (5,4), (1,1), (1,1000)]
  | .a_half => [(1,2), (1651,2500), (1,4), (8,25), (1,1), (1,1000)]
  | .a_p06 => [(3,5), (2643,5000), (1,4), (0,1), (1,1), (1,1000)]
  | .b_third => [(1,3), (8527,10000), (1,8), (47,20), (1,10), (1,1000)]
  | .b_p042 => [(21,50), (7583,10000), (1,8), (89,100), (1,10), (1,1000)]
  | .b_half => [(1,2), (1651,2500), (1,8), (13,50), (1,10), (1,1000)]
  | .b_p06 => [(3,5), (2643,5000), (1,8), (0,1), (1,10), (1,1000)]
  | .d_third => [(1,3), (8527,10000), (1,6), (237,100), (1,10), (1,10000)]
  | .d_p042 => [(21,50), (7583,10000), (1,6), (7,8), (1,10), (1,10000)]
  | .d_half => [(1,2), (1651,2500), (1,6), (221,1000), (1,10), (1,10000)]
  | .d_p052 => [(13,25), (6337,10000), (1,6), (127,1000), (1,10), (1,10000)]
  | .g_third => [(1,3), (8527,10000), (1,4), (7,3), (1,1), (1,1000)]
  | .g_p042 => [(21,50), (7583,10000), (1,4), (17,25), (1,1), (1,1000)]
  | .g_p044 => [(11,25), (1833,2500), (1,4), (49,100), (1,1), (1,1000)]
  | .h_third => [(1,3), (8527,10000), (7,25), (21,10), (1,10), (1,1000)]
  | .h_p038 => [(19,50), (4009,5000), (7,25), (26,25), (1,10), (1,1000)]
  | .e_third => [(1,3), (8527,10000), (7,25), (2,1), (1,10), (1,1000)]
  | .e_p038 => [(19,50), (4009,5000), (7,25), (26,25), (1,10), (1,1000)]
  | .e_p042 => [(21,50), (7583,10000), (7,25), (3,5), (1,10), (1,1000)]
  | .e_p044 => [(11,25), (1833,2500), (7,25), (21,50), (1,10), (1,1000)]
  | .e_half => [(1,2), (1651,2500), (7,25), (9,50), (1,10), (1,1000)]
  | .e_p052 => [(13,25), (6337,10000), (7,25), (3,25), (1,10), (1,1000)]
  | .e_p06 => [(3,5), (2643,5000), (7,25), (0,1), (1,10), (1,1000)]

def fiberProfileControlCoefficientFraction (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) : lowMeanFraction :=
  let r := fiberProfileControlById id
  match role with
  | .c0 => r.c0
  | .c1 => r.c1
  | .c2 => r.c2
  | .firstTest => r.e1
  | .secondTest => r.e2

def fiberProfileControlRelation (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) (x : lowMeanFraction) : Prop :=
  let f := fiberProfileControlCoefficientFraction id role
  lowMeanFractionValid f ∧
    match role with
    | .c0 | .c2 => lowMeanFractionEq x f
    | .c1 => lowMeanFractionEq x f ∧ lowMeanFractionLT (0,1) x
    | .firstTest | .secondTest => lowMeanFractionLE f x ∧ lowMeanFractionLT (0,1) f

instance fiberProfileControlRelationDecidable (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) (x : lowMeanFraction) :
    Decidable (fiberProfileControlRelation id role x) := by
  cases role <;> dsimp [fiberProfileControlRelation] <;> infer_instance

def fiberProfileControlCheck (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) : Bool :=
  let r := fiberProfileControlById id
  lowMeanIntegerShapeCheck (fiberProfileControlExpr id role) (fiberProfileControlShape id role) &&
    decide (r.printed = fiberProfileControlPrinted id ∧
      fiberProfileControlParameters r = fiberProfileControlExpectedParameters id ∧
      fiberProfileControlRelation id role (lowMeanIntegerExprValue (fiberProfileControlExpr id role)))

def fiberProfileControlIndex : FiberProfileControlIdentity → ℕ
  | .a_third => 0
  | .a_p042 => 1
  | .a_half => 2
  | .a_p06 => 3
  | .b_third => 4
  | .b_p042 => 5
  | .b_half => 6
  | .b_p06 => 7
  | .d_third => 8
  | .d_p042 => 9
  | .d_half => 10
  | .d_p052 => 11
  | .g_third => 12
  | .g_p042 => 13
  | .g_p044 => 14
  | .h_third => 15
  | .h_p038 => 16
  | .e_third => 17
  | .e_p038 => 18
  | .e_p042 => 19
  | .e_p044 => 20
  | .e_half => 21
  | .e_p052 => 22
  | .e_p06 => 23

def fiberProfileControlRoleIndex : FiberProfileControlRole → ℕ
  | .c0 => 0
  | .c1 => 1
  | .c2 => 2
  | .firstTest => 3
  | .secondTest => 4

theorem fiber_profile_control_checks :
    (List.range 120).all (fun k => fiberProfileControlCheck
      (fiberProfileControlIdentityAt (k / 5)) (fiberProfileControlRoleAt (k % 5))) = true := by
  decide +kernel

theorem fiber_profile_control_index_checked {k : ℕ} (hk : k < 120) :
    fiberProfileControlCheck (fiberProfileControlIdentityAt (k / 5))
      (fiberProfileControlRoleAt (k % 5)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_profile_control_checks k hk

theorem fiber_profile_control_named_checked (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) : fiberProfileControlCheck id role = true := by
  let k := 5 * fiberProfileControlIndex id + fiberProfileControlRoleIndex role
  have hk : k < 120 := by cases id <;> cases role <;> decide +kernel
  have h := fiber_profile_control_index_checked hk
  have hb : fiberProfileControlIdentityAt (k / 5) = id ∧
      fiberProfileControlRoleAt (k % 5) = role := by
    cases id <;> cases role <;>
      norm_num [k,fiberProfileControlIndex,fiberProfileControlRoleIndex,
        fiberProfileControlIdentityAt,fiberProfileControlRoleAt]
  rw [hb.1,hb.2] at h
  exact h

theorem fiber_profile_control_shape_sound (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberProfileControlExpr id role)) ∧
      fiberProfileControlValue id role = lowMeanFractionReal
        (lowMeanIntegerExprValue (fiberProfileControlExpr id role)) := by
  have h := fiber_profile_control_named_checked id role
  simp only [fiberProfileControlCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_profile_control_shape_real] at hs
  exact hs

theorem fiber_profile_control_c1_positive (id : FiberProfileControlIdentity) :
    0 < (fiberProfileControlCoefficients id).2.1 := by
  have h := fiber_profile_control_named_checked id .c1
  simp only [fiberProfileControlCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  simp only [fiberProfileControlRelation] at hd
  have hs := fiber_profile_control_shape_sound id .c1
  change 0 < fiberProfileControlValue id .c1
  rw [hs.2]
  have hc := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hs.1).mp hd.2.2.2.2
  simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hc

theorem fiber_profile_control_test_bound (id : FiberProfileControlIdentity)
    (role : FiberProfileControlRole) (hr : role = .firstTest ∨ role = .secondTest) :
    lowMeanFractionReal (fiberProfileControlCoefficientFraction id role) ≤
      fiberProfileControlValue id role ∧
      0 < lowMeanFractionReal (fiberProfileControlCoefficientFraction id role) := by
  have h := fiber_profile_control_named_checked id role
  simp only [fiberProfileControlCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_profile_control_shape_sound id role
  have hc : lowMeanFractionValid (fiberProfileControlCoefficientFraction id role) ∧
      lowMeanFractionLE (fiberProfileControlCoefficientFraction id role)
        (lowMeanIntegerExprValue (fiberProfileControlExpr id role)) ∧
      lowMeanFractionLT (0,1) (fiberProfileControlCoefficientFraction id role) := by
    rcases hr with rfl | rfl <;> exact hd.2.2
  constructor
  · rw [hs.2]
    exact (lowMean_fraction_le_iff hc.1 hs.1).mp hc.2.1
  · have hh := (lowMean_fraction_lt_iff (by decide +kernel : lowMeanFractionValid (0,1)) hc.1).mp hc.2.2
    simpa only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] using hh

end Erdos993Lean.Analytic.V213
