module

public import Erdos993Lean.Analytic.V213.FiberBudgetRestCheck
public import Erdos993Lean.Analytic.V213.FiberInputDomain

/-!
All55 actual F17 input-to-block bindings. D, theta and the starting mean
are read from accepted Part1 records. Both exact accepted N44 endpoints
are used for the absolute-skew containment; z comes from actual F16.
All comparisons use Int/Nat and grouped decide +kernel/F4Fast. No second
list of55 epsilon values is introduced.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberBudgetInputTests (id : FiberInputIdentity) : Prop :=
  let r := fiberBudgetById (fiberInputBudget id)
  let p := fiberInputPaperRow id
  let lo := fiberInputSignedSkewFraction (fiberInputQloFraction id)
  let hi := fiberInputSignedSkewFraction (fiberInputQhiFraction id)
  r.inputLo ≤ (fiberInputRouteById id).iota ∧ (fiberInputRouteById id).iota ≤ r.inputHi ∧
  lowMeanFractionValid p.mu0 ∧ lowMeanFractionValid p.theta ∧ lowMeanFractionValid p.D ∧
  lowMeanFractionValid lo ∧ lowMeanFractionValid hi ∧
  lowMeanFractionEq p.mu0 (fiberInputRouteById id).mu0 ∧
  lowMeanFractionEq r.b (fiberInputClassB (fiberInputRouteById id).kind) ∧
  lowMeanFractionLE r.mu_star (fiberInputRouteById id).mu0 ∧
  lowMeanFractionLE p.theta r.Theta ∧ lowMeanFractionLE p.D r.D_star ∧
  lowMeanFractionLE (lowMeanFractionAbs lo) r.R ∧ lowMeanFractionLE (lowMeanFractionAbs hi) r.R ∧
  lowMeanFractionLE (fiberInputPriceFraction id) r.Z ∧ lowMeanFractionLE r.R (1,2) ∧
  lowMeanFractionLE (0,1) p.D ∧ lowMeanFractionLE (0,1) p.theta

instance fiberBudgetInputTestsDecidable (id : FiberInputIdentity) :
    Decidable (fiberBudgetInputTests id) := by unfold fiberBudgetInputTests; infer_instance

theorem fiber_budget_input_checks :
    (List.range 55).all (fun k => decide (fiberBudgetInputTests (fiberInputIdentityAt k))) = true := by
  decide +kernel

theorem fiber_budget_input_facts (id : FiberInputIdentity) : fiberBudgetInputTests id := by
  have hk : fiberInputIndex id < 55 := by cases id <;> decide +kernel
  have he : fiberInputIdentityAt (fiberInputIndex id) = id := by cases id <;> rfl
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_budget_input_checks (fiberInputIndex id) hk
  rw [he] at h
  exact of_decide_eq_true h

end Erdos993Lean.Analytic.V213
