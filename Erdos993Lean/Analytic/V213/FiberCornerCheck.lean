module

public import Erdos993Lean.Analytic.V213.FiberCornerShape
public import Erdos993Lean.Analytic.V213.FiberWindowCheck

/-!
Whole-number certification of all58 complete F14/F13 trees.
Every grouped range is consumed through F4Fast. Metadata binds actual
input identities/rates/endpoints and actual window/corner associations.
The comparisons use Int/Nat cross-products, with no Rat kernel test.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberCornerEquality (e : LowMeanIntegerExpr) (v : lowMeanFraction) : Prop :=
  lowMeanFractionValid v ∧ lowMeanFractionEq (lowMeanIntegerExprValue e) v

instance fiberCornerEqualityDecidable (e : LowMeanIntegerExpr) (v : lowMeanFraction) :
    Decidable (fiberCornerEquality e v) := by unfold fiberCornerEquality; infer_instance

def fiberCornerLogTests (id : FiberCornerLogIdentity) (gap : Bool) : Prop :=
  let r := fiberCornerLogById id
  r.printed = fiberCornerLogPrinted id ∧
  lowMeanFractionValid r.y ∧ lowMeanFractionValid r.L ∧ lowMeanFractionValid r.gap ∧
  lowMeanFractionLE ((2 : ℤ)^r.n,1) r.y ∧ lowMeanFractionLT r.y ((2 : ℤ)^(r.n+1),1) ∧
  lowMeanFractionLT (0,1) r.gap ∧
  (if gap then lowMeanFractionLE r.gap (lowMeanIntegerExprValue (fiberCornerLogExpr id gap))
   else fiberCornerEquality (fiberCornerLogExpr id gap) r.upper)

instance fiberCornerLogTestsDecidable (id : FiberCornerLogIdentity) (gap : Bool) :
    Decidable (fiberCornerLogTests id gap) := by unfold fiberCornerLogTests; infer_instance

def fiberCornerLogCheck (id : FiberCornerLogIdentity) (gap : Bool) : Bool :=
  lowMeanIntegerShapeCheck (fiberCornerLogExpr id gap) (fiberCornerLogShape id gap) &&
    decide (fiberCornerLogTests id gap)

def fiberCornerRateTests (id : FiberCornerRateIdentity) : Prop :=
  let r := fiberCornerRateById id
  r.printed = fiberCornerRatePrinted id ∧
  fiberInputIndex r.input = fiberCornerRateIndex id ∧
  r.ell0 = (fiberInputRouteById r.input).ell0 ∧ r.lambda_hi = fiberInputHiFraction r.input ∧
  lowMeanFractionValid r.base ∧ lowMeanFractionValid r.slope ∧ lowMeanFractionValid r.ell0 ∧
  lowMeanFractionValid r.lambda_hi ∧ lowMeanFractionLT (0,1) r.slack ∧
  fiberCornerEquality (fiberCornerRateExpr id) r.slack

instance fiberCornerRateTestsDecidable (id : FiberCornerRateIdentity) :
    Decidable (fiberCornerRateTests id) := by unfold fiberCornerRateTests; infer_instance

def fiberCornerRateCheck (id : FiberCornerRateIdentity) : Bool :=
  lowMeanIntegerShapeCheck (fiberCornerRateExpr id) (fiberCornerRateShape id) &&
    decide (fiberCornerRateTests id)

def fiberRateCornerTests (id : FiberRateCornerIdentity) : Prop :=
  let r := fiberRateCornerById id
  r.printed = fiberRateCornerPrinted id ∧
  lowMeanFractionValid r.ell ∧ lowMeanFractionValid r.L ∧ lowMeanFractionValid r.ts ∧
  lowMeanFractionLT (0,1) r.gap ∧ fiberCornerEquality (fiberRateCornerExpr id) r.gap

instance fiberRateCornerTestsDecidable (id : FiberRateCornerIdentity) :
    Decidable (fiberRateCornerTests id) := by unfold fiberRateCornerTests; infer_instance

def fiberRateCornerCheck (id : FiberRateCornerIdentity) : Bool :=
  lowMeanIntegerShapeCheck (fiberRateCornerExpr id) (fiberRateCornerShape id) &&
    decide (fiberRateCornerTests id)

def fiberWindowWeightTests (id : FiberWindowWeightIdentity) (gap : Bool) : Prop :=
  let r := fiberWindowWeightById id
  let w := fiberWindowById r.window
  let c := fiberWindowCornerById r.corner
  r.printed = fiberWindowWeightPrinted id ∧
  fiberWindowIndex r.window = fiberWindowWeightIndex id + 2 ∧
  w.outerClass = c.outerClass ∧
  c.printed = fiberWindowCornerPrinted r.corner ∧
  lowMeanFractionValid w.L_W ∧ lowMeanFractionValid w.h ∧
  lowMeanFractionValid c.mu_c ∧ lowMeanFractionValid c.ell_c ∧ lowMeanFractionValid c.L_c ∧
  lowMeanFractionValid c.Z_W ∧ lowMeanFractionValid r.y ∧ lowMeanFractionValid r.epsilon ∧
  lowMeanFractionEq (lowMeanFractionMul r.y c.Z_W) w.L_W ∧
  lowMeanFractionLE ((2 : ℤ)^r.n,1) r.y ∧ lowMeanFractionLT r.y ((2 : ℤ)^(r.n+1),1) ∧
  lowMeanFractionLT (0,1) c.Z_W ∧ lowMeanFractionLT (0,1) r.epsilon ∧
  r.epsilon = c.epsilon_W ∧
  fiberCornerEquality (fiberWindowWeightExpr id gap) (if gap then r.gap else r.upper) ∧
  (gap = true → lowMeanFractionLE r.epsilon r.gap)

instance fiberWindowWeightTestsDecidable (id : FiberWindowWeightIdentity) (gap : Bool) :
    Decidable (fiberWindowWeightTests id gap) := by unfold fiberWindowWeightTests; infer_instance

def fiberWindowWeightCheck (id : FiberWindowWeightIdentity) (gap : Bool) : Bool :=
  lowMeanIntegerShapeCheck (fiberWindowWeightExpr id gap) (fiberWindowWeightShape id gap) &&
    decide (fiberWindowWeightTests id gap)

theorem fiber_corner_log_checks :
    (List.range 26).all (fun k => fiberCornerLogCheck (fiberCornerLogIdentityAt (k/2)) (k%2==1)) = true := by
  decide +kernel

theorem fiber_corner_rate_checks :
    (List.range 6).all (fun k => fiberCornerRateCheck (fiberCornerRateIdentityAt k)) = true := by
  decide +kernel

theorem fiber_rate_corner_checks :
    (List.range 10).all (fun k => fiberRateCornerCheck (fiberRateCornerIdentityAt k)) = true := by
  decide +kernel

theorem fiber_window_weight_checks :
    (List.range 16).all (fun k => fiberWindowWeightCheck (fiberWindowWeightIdentityAt (k/2)) (k%2==1)) = true := by
  decide +kernel

theorem fiber_corner_log_checked (id : FiberCornerLogIdentity) (gap : Bool) :
    fiberCornerLogCheck id gap = true := by
  let k := fiberCornerLogIndex id*2 + if gap then 1 else 0
  have hk : k < 26 := by cases id <;> cases gap <;> decide +kernel
  have hi : fiberCornerLogIdentityAt (k/2) = id ∧ (k%2==1) = gap := by
    cases id <;> cases gap <;> norm_num [k,fiberCornerLogIndex,fiberCornerLogIdentityAt]
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_corner_log_checks k hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_corner_rate_checked (id : FiberCornerRateIdentity) : fiberCornerRateCheck id = true := by
  have hk : fiberCornerRateIndex id < 6 := by cases id <;> decide +kernel
  have hi : fiberCornerRateIdentityAt (fiberCornerRateIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_corner_rate_checks _ hk
  rw [hi] at h
  exact h

theorem fiber_rate_corner_checked (id : FiberRateCornerIdentity) : fiberRateCornerCheck id = true := by
  have hk : fiberRateCornerIndex id < 10 := by cases id <;> decide +kernel
  have hi : fiberRateCornerIdentityAt (fiberRateCornerIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_rate_corner_checks _ hk
  rw [hi] at h
  exact h

theorem fiber_window_weight_checked (id : FiberWindowWeightIdentity) (gap : Bool) :
    fiberWindowWeightCheck id gap = true := by
  let k := fiberWindowWeightIndex id*2 + if gap then 1 else 0
  have hk : k < 16 := by cases id <;> cases gap <;> decide +kernel
  have hi : fiberWindowWeightIdentityAt (k/2) = id ∧ (k%2==1) = gap := by
    cases id <;> cases gap <;> norm_num [k,fiberWindowWeightIndex,fiberWindowWeightIdentityAt]
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_window_weight_checks k hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_corner_equality_real {e : LowMeanIntegerExpr} {s : LowMeanIntegerShape}
    {v : lowMeanFraction} (hs : lowMeanIntegerShapeCheck e s = true)
    (hv : fiberCornerEquality e v) : lowMeanIntegerShapeReal s = lowMeanFractionReal v := by
  have h := lowMean_integerShape_sound hs
  exact h.2.trans ((lowMean_fraction_eq_iff h.1 hv.1).mp hv.2)

theorem fiber_corner_log_facts (id : FiberCornerLogIdentity) (gap : Bool) :
    fiberCornerLogTests id gap := by
  have h := fiber_corner_log_checked id gap
  simp only [fiberCornerLogCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

theorem fiber_corner_rate_facts (id : FiberCornerRateIdentity) : fiberCornerRateTests id := by
  have h := fiber_corner_rate_checked id
  simp only [fiberCornerRateCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

theorem fiber_rate_corner_facts (id : FiberRateCornerIdentity) : fiberRateCornerTests id := by
  have h := fiber_rate_corner_checked id
  simp only [fiberRateCornerCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

theorem fiber_window_weight_facts (id : FiberWindowWeightIdentity) (gap : Bool) :
    fiberWindowWeightTests id gap := by
  have h := fiber_window_weight_checked id gap
  simp only [fiberWindowWeightCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

end Erdos993Lean.Analytic.V213
