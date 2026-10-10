module

public import Erdos993Lean.Analytic.V213.FiberOuterRegionData

/-!
All eight printed outer class starts. Typed printed identities bind
input spans, all row fields, actual universal/four-row routes and exact
mu_D*tau+2 widths. The checker uses Int/Nat only; indices enumerate the
complete family and F4Fast exposes each named class without list authority.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

def fiberOuterClassFields (r : FiberOuterClassRow) : List lowMeanFraction :=
  [r.skew_lower,r.skew_upper,r.b,r.beta_prime,r.tau,r.mu_D,
    r.minimum_N,r.required_N,r.required_skew_lower,r.required_skew_upper,r.required_tau]

def fiberOuterClassExpected : FiberOuterClassIdentity → ℕ × ℕ × List lowMeanFraction
  | .c1 => (0,2,[(3793,10000),(1,2),(2,5),(0,1),(3,5),(45,1),(29,1),(26,1),(1,4),(1,2),(3,5)])
  | .c2 => (3,5,[(1,4),(1897,5000),(2,5),(0,1),(69,100),(50,1),(73,2),(26,1),(1,4),(1,2),(3,5)])
  | .c3 => (40,43,[(833,5000),(2309,10000),(0,1),(1,2),(11,25),(50,1),(24,1),(24,1),(4,25),(2,5),(11,25)])
  | .c4 => (44,46,[(2307,10000),(341,1250),(3,20),(3,10),(21,50),(40,1),(94,5),(18,1),(9,40),(2,5),(21,50)])
  | .c5 => (47,49,[(2727,10000),(194,625),(3,10),(0,1),(2,5),(50,1),(22,1),(20,1),(4,15),(2,5),(9,25)])
  | .c6 => (50,52,[(3103,10000),(861,2500),(3,10),(0,1),(9,25),(50,1),(20,1),(20,1),(4,15),(2,5),(9,25)])
  | .c7 => (53,53,[(1721,5000),(3847,10000),(3,10),(1,1),(33,100),(50,1),(37,2),(17,1),(17,50),(2,5),(3,10)])
  | .c8 => (54,54,[(1923,5000),(2,5),(3,10),(1,1),(3,10),(50,1),(17,1),(17,1),(17,50),(2,5),(3,10)])

def fiberOuterClassPrinted : FiberOuterClassIdentity → String
  | .c1 => "F05:class:C1" | .c2 => "F05:class:C2" | .c3 => "F05:class:C3"
  | .c4 => "F05:class:C4" | .c5 => "F05:class:C5" | .c6 => "F05:class:C6"
  | .c7 => "F05:class:C7" | .c8 => "F05:class:C8"

def fiberOuterClassRouteFields (r : FiberOuterClassRow) : List lowMeanFraction :=
  match r.start with
  | none => [fiberOuterUniversal.minimum_N,fiberOuterUniversal.skew_lower,
      fiberOuterUniversal.skew_upper,fiberOuterUniversal.minimum_t,
      fiberOuterUniversal.b_upper,fiberOuterUniversal.beta_lower]
  | some id => let s := fiberOuterStartById id
      [s.n,s.a,(2,5),s.sigma,s.b0,s.beta0]

def fiberOuterClassActualRouteFields (r : FiberOuterClassRow) : List lowMeanFraction :=
  [r.required_N,r.required_skew_lower,r.required_skew_upper,r.required_tau,
    (match r.start with | none => (2,5) | some id => (fiberOuterStartById id).b0),
    (match r.start with | none => (0,1) | some id => (fiberOuterStartById id).beta0)]

def fiberOuterClassRouteName (r : FiberOuterClassRow) : String :=
  match r.start with
  | none => fiberOuterUniversal.printed
  | some id => fiberOuterStartPrinted id

def fiberOuterClassRouteKey (id : FiberOuterClassIdentity) (r : FiberOuterClassRow) : Bool :=
  match id,r.start with
  | .c1,none | .c2,none | .c3,some .c3 | .c4,some .c4
  | .c5,some .c5c6 | .c6,some .c5c6 | .c7,some .c7c8 | .c8,some .c7c8 => true
  | _,_ => false

def fiberOuterClassTargetGuard (r : FiberOuterClassRow) : Prop :=
  match r.start with
  | none => lowMeanFractionLE r.b (2,5) ∧ lowMeanFractionLE (0,1) r.beta_prime
  | some k => lowMeanFractionLE r.b (fiberOuterStartById k).b0 ∧
      lowMeanFractionLE (fiberOuterStartById k).beta0 r.beta_prime

instance fiberOuterClassTargetGuardDecidable (r : FiberOuterClassRow) :
    Decidable (fiberOuterClassTargetGuard r) := by
  cases h : r.start <;> dsimp [fiberOuterClassTargetGuard] <;> rw [h] <;> infer_instance

def fiberOuterClassCheck (id : FiberOuterClassIdentity) : Bool :=
  let r := fiberOuterClassById id
  let expected := fiberOuterClassExpected id
  fiberOuterClassRouteKey id r && decide (
    r.printed = fiberOuterClassPrinted id ∧ r.input_lo = expected.1 ∧ r.input_hi = expected.2.1 ∧
    fiberOuterClassFields r = expected.2.2 ∧ r.regionPrinted = fiberOuterClassRouteName r ∧
    fiberOuterClassActualRouteFields r = fiberOuterClassRouteFields r ∧
    (fiberOuterClassFields r).all (fun x => decide (lowMeanFractionValid x)) = true ∧
    lowMeanFractionEq r.minimum_N (lowMeanFractionAdd (lowMeanFractionMul r.mu_D r.tau) (2,1)) ∧
    lowMeanFractionLE r.required_N r.minimum_N ∧
    lowMeanFractionLE r.required_skew_lower r.skew_lower ∧
    lowMeanFractionLE r.skew_upper r.required_skew_upper ∧
    lowMeanFractionLE r.required_tau r.tau ∧
    lowMeanFractionLE (4,25) r.skew_lower ∧ lowMeanFractionLE r.skew_upper (1,2) ∧
    lowMeanFractionLE (0,1) r.b ∧ lowMeanFractionLE r.b (2,5) ∧
    lowMeanFractionLE (0,1) r.beta_prime ∧ lowMeanFractionLE r.beta_prime (1,1) ∧
    lowMeanFractionLE (40,1) r.mu_D ∧ lowMeanFractionLT (0,1) r.tau ∧
    fiberOuterClassTargetGuard r)

theorem fiber_outer_class_checks :
    (List.range 8).all (fun k => fiberOuterClassCheck (fiberOuterClassIdentityAt k)) = true := by
  decide +kernel

theorem fiber_outer_class_index {k : ℕ} (hk : k < 8) :
    fiberOuterClassCheck (fiberOuterClassIdentityAt k) = true :=
  Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_outer_class_checks k hk

theorem fiber_outer_class_named (id : FiberOuterClassIdentity) : fiberOuterClassCheck id = true := by
  cases id <;> decide +kernel

end Erdos993Lean.Analytic.V213
