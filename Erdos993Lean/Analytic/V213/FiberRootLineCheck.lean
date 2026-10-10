module

public import Erdos993Lean.Analytic.V213.FiberRootLineShape

/-!
Accepted F09 named-piece kernel checks. Complete canonical shapes,
all source parameters, positive denominators, dyadic input guards and
both strict printed gaps are checked with Int/Nat arithmetic. Indexed
range checks only enumerate the three printed identities.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberRootLineParameters (r : FiberRootLineRow) : List lowMeanFraction :=
  [r.lo,r.hi,r.v,r.k,r.alpha,r.beta,r.epsilon_r,r.epsilon_c]

def fiberRootLineExpectedParameters : FiberRootLineIdentity → List lowMeanFraction
  | .third_042 => [(1,3),(21,50),(4,5),(5,12),(73,60),(273,250),(1,10000),(1,10)]
  | .p042_half => [(21,50),(1,2),(18,25),(35,64),(2027,1600),(1213,1000),(1,1000),(1,10)]
  | .half_p06 => [(1,2),(3,5),(59,100),(205,282),(18569,14100),(657,500),(1,1000),(1,100)]

def fiberRootLineExpectedN : FiberRootLineIdentity → ℕ
  | .third_042 | .p042_half => 2
  | .half_p06 => 1

def fiberRootLineArgumentFraction (id : FiberRootLineIdentity) : lowMeanFraction :=
  let r := fiberRootLineById id
  lowMeanFractionMul (lowMeanFractionPow (lowMeanFractionAdd (1,1) (lowMeanFractionNeg r.v)) 2)
    (lowMeanFractionPow (r.beta.1 * r.k.2,r.beta.2 * r.k.1.toNat) 5)

def fiberRootLineThreshold (id : FiberRootLineIdentity) : FiberRootLineRole → lowMeanFraction
  | .logarithm => (0,1)
  | .rootGap => (fiberRootLineById id).epsilon_r
  | .convexityGap => (fiberRootLineById id).epsilon_c

def fiberRootLineRelation (id : FiberRootLineIdentity) (role : FiberRootLineRole)
    (x : lowMeanFraction) : Prop :=
  lowMeanFractionValid (fiberRootLineThreshold id role) ∧
    match role with
    | .logarithm => True
    | .rootGap | .convexityGap => lowMeanFractionLT (fiberRootLineThreshold id role) x

instance fiberRootLineRelationDecidable (id : FiberRootLineIdentity) (role : FiberRootLineRole)
    (x : lowMeanFraction) : Decidable (fiberRootLineRelation id role x) := by
  cases role <;> dsimp [fiberRootLineRelation] <;> infer_instance

def fiberRootLineCheck (id : FiberRootLineIdentity) (role : FiberRootLineRole) : Bool :=
  let r := fiberRootLineById id
  lowMeanIntegerShapeCheck (fiberRootLineExpr id role) (fiberRootLineShape id role) &&
    decide (r.printed = fiberRootLinePrinted id ∧
      fiberRootLineParameters r = fiberRootLineExpectedParameters id ∧
      r.n = fiberRootLineExpectedN id ∧
      fiberRootLineRelation id role (lowMeanIntegerExprValue (fiberRootLineExpr id role)))

theorem fiber_root_line_checks :
    (List.range 9).all (fun k => fiberRootLineCheck (fiberRootLineIdentityAt (k / 3))
      (fiberRootLineRoleAt (k % 3))) = true := by
  decide +kernel

theorem fiber_root_line_index_checked {k : ℕ} (hk : k < 9) :
    fiberRootLineCheck (fiberRootLineIdentityAt (k / 3)) (fiberRootLineRoleAt (k % 3)) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_root_line_checks k hk

theorem fiber_root_line_named_checked (id : FiberRootLineIdentity) (role : FiberRootLineRole) :
    fiberRootLineCheck id role = true := by
  cases id <;> cases role <;> decide +kernel

theorem fiber_root_line_shape_sound (id : FiberRootLineIdentity) (role : FiberRootLineRole) :
    lowMeanFractionValid (lowMeanIntegerExprValue (fiberRootLineExpr id role)) ∧
      fiberRootLineValue id role = lowMeanFractionReal (lowMeanIntegerExprValue (fiberRootLineExpr id role)) := by
  have h := fiber_root_line_named_checked id role
  simp only [fiberRootLineCheck,Bool.and_eq_true] at h
  have hs := lowMean_integerShape_sound h.1
  rw [fiber_root_line_shape_real] at hs
  exact hs

theorem fiber_root_line_strict_gap (id : FiberRootLineIdentity) (role : FiberRootLineRole)
    (hr : role ≠ .logarithm) :
    lowMeanFractionReal (fiberRootLineThreshold id role) < fiberRootLineValue id role := by
  have h := fiber_root_line_named_checked id role
  simp only [fiberRootLineCheck,Bool.and_eq_true] at h
  have hd := of_decide_eq_true h.2
  have hs := fiber_root_line_shape_sound id role
  have hc : lowMeanFractionValid (fiberRootLineThreshold id role) ∧
      lowMeanFractionLT (fiberRootLineThreshold id role)
        (lowMeanIntegerExprValue (fiberRootLineExpr id role)) := by
    have hh := hd.2.2.2
    cases role with
    | logarithm => exact False.elim (hr rfl)
    | rootGap => exact hh
    | convexityGap => exact hh
  rw [hs.2]
  exact (lowMean_fraction_lt_iff hc.1 hs.1).mp hc.2

def fiberRootLineInputCheck (id : FiberRootLineIdentity) : Bool :=
  let y := fiberRootLineArgumentFraction id
  decide (lowMeanFractionValid y ∧ lowMeanFractionLE ((2 : ℤ) ^ (fiberRootLineById id).n,1) y)

theorem fiber_root_line_inputs :
    (List.range 3).all (fun k => fiberRootLineInputCheck (fiberRootLineIdentityAt k)) = true := by
  decide +kernel

theorem fiber_root_line_input_checked (id : FiberRootLineIdentity) :
    fiberRootLineInputCheck id = true := by
  cases id <;> decide +kernel

theorem fiber_root_line_argument_fraction_real (id : FiberRootLineIdentity) :
    lowMeanFractionReal (fiberRootLineArgumentFraction id) = fiberRootLineArgument id := by
  cases id <;> norm_num [fiberRootLineArgumentFraction,fiberRootLineById,fiberRootLineArgument,
    lowMeanFractionReal,lowMeanFractionMul,lowMeanFractionPow,lowMeanFractionAdd,lowMeanFractionNeg]

theorem fiber_root_line_argument_domain (id : FiberRootLineIdentity) :
    (2 : ℝ) ^ (fiberRootLineById id).n ≤ fiberRootLineArgument id := by
  have h := fiber_root_line_input_checked id
  simp only [fiberRootLineInputCheck,decide_eq_true_eq] at h
  have hc := (lowMean_fraction_le_iff (by exact Nat.zero_lt_one) h.1).mp h.2
  rw [fiber_root_line_argument_fraction_real] at hc
  simpa only [lowMeanFractionReal,Int.cast_pow,Int.cast_ofNat,Nat.cast_one,div_one,
    ] using hc

end Erdos993Lean.Analytic.V213
