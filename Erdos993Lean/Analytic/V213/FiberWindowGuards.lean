module

public import Erdos993Lean.Analytic.V213.FiberWindowCheck

/-!
Complete printed-window analytic domains. Grouped Int/Nat checks
retain positive denominators, actual class means/skews/targets, anchors,
closed time endpoints and N0=mu_D*l+2. No window is certified by sampling.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberWindowGuard (id : FiberWindowIdentity) : Prop :=
  let r := fiberWindowById id
  let c := fiberOuterClassById r.outerClass
  ([r.l,r.h,r.N0,r.v,r.X,r.L_W,c.skew_lower,c.skew_upper,c.b,c.beta_prime,c.mu_D]).all
    (fun x => decide (lowMeanFractionValid x)) = true ∧
  lowMeanFractionLE (23,100) c.skew_lower ∧ lowMeanFractionLE c.skew_upper (1,2) ∧
  lowMeanFractionLE (14,1) r.N0 ∧ lowMeanFractionLT (0,1) r.l ∧
  lowMeanFractionLT (0,1) r.v ∧ lowMeanFractionLE r.l r.h ∧
  lowMeanFractionLE r.h (69,100) ∧ lowMeanFractionLE (40,1) c.mu_D ∧
  lowMeanFractionLE (0,1) c.b ∧ lowMeanFractionLE c.b (2,5) ∧
  lowMeanFractionLE (0,1) c.beta_prime ∧ lowMeanFractionLE c.beta_prime (1,1) ∧
  lowMeanFractionLE (0,1) r.L_W ∧
  lowMeanFractionEq r.N0 (lowMeanFractionAdd (lowMeanFractionMul c.mu_D r.l) (2,1))

instance fiberWindowGuardDecidable (id : FiberWindowIdentity) : Decidable (fiberWindowGuard id) := by
  unfold fiberWindowGuard
  infer_instance

theorem fiber_window_guard_checks :
    (List.range 10).all (fun k => decide (fiberWindowGuard (fiberWindowIdentityAt k))) = true := by
  decide +kernel

theorem fiber_window_guard_checked (id : FiberWindowIdentity) : fiberWindowGuard id := by
  have hk : fiberWindowIndex id < 10 := by cases id <;> decide +kernel
  have hi : fiberWindowIdentityAt (fiberWindowIndex id) = id := by
    cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_window_guard_checks _ hk
  rw [hi] at h
  exact of_decide_eq_true h

/-- Exact real domains of the same checked printed constants. -/
theorem fiber_window_real_guards (id : FiberWindowIdentity) :
    let r := fiberWindowById id
    let c := fiberOuterClassById r.outerClass
    fiberWindowN0 id = lowMeanFractionReal r.N0 ∧
    23/100 ≤ lowMeanFractionReal c.skew_lower ∧
    lowMeanFractionReal c.skew_upper ≤ 1/2 ∧
    14 ≤ fiberWindowN0 id ∧ 0 < lowMeanFractionReal r.l ∧ 0 < lowMeanFractionReal r.v ∧
    lowMeanFractionReal r.h ≤ 69/100 ∧ 40 ≤ lowMeanFractionReal c.mu_D ∧
    0 ≤ lowMeanFractionReal c.b ∧ lowMeanFractionReal c.b ≤ 2/5 ∧
    0 ≤ lowMeanFractionReal c.beta_prime ∧ lowMeanFractionReal c.beta_prime ≤ 1 ∧
    0 ≤ lowMeanFractionReal r.L_W := by
  have hchecked := fiber_window_guard_checked id
  cases id <;> norm_num [fiberWindowN0,fiberWindowById,fiberOuterClassById,lowMeanFractionReal]

theorem fiber_window_minorant_checked (id : FiberWindowIdentity) :
    let r := fiberWindowById id
    let c := fiberOuterClassById r.outerClass
    lowMeanFractionReal r.X < fiberWindowX (lowMeanFractionReal c.skew_lower)
      (lowMeanFractionReal c.skew_upper) (fiberWindowN0 id)
      (lowMeanFractionReal r.l) (lowMeanFractionReal r.v) := by
  have h := fiber_window_gap_checked id
  have hp := fiber_window_epsilon_positive id
  simp only [fiberWindowValue] at h
  dsimp only
  linarith only [h,hp]

theorem fiber_window_price_value (id : FiberWindowIdentity) :
    let r := fiberWindowById id
    let c := fiberOuterClassById r.outerClass
    fiberWindowPrice (lowMeanFractionReal c.b) (lowMeanFractionReal c.beta_prime)
      (lowMeanFractionReal r.l) (lowMeanFractionReal r.h) (fiberWindowN0 id)
      (lowMeanFractionReal r.X) = lowMeanFractionReal r.L_W :=
  fiber_window_value_checked id .price

end Erdos993Lean.Analytic.V213
