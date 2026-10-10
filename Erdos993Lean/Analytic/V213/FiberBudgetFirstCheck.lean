module

public import Erdos993Lean.Analytic.V213.FiberBudgetShape

/-!
First seven of the thirteen printed F17 budget rows.  Complete
canonical trees and strict inequalities are checked over Int/Nat using
grouped Range.all and decide +kernel.  Remaining six rows belong to the
separate checker.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberBudgetRoleAt : ℕ → FiberBudgetRole
  | 0 => .budget | 1 => .strictGap | _ => .margin

def fiberBudgetRoleIndex : FiberBudgetRole → ℕ
  | .budget => 0 | .strictGap => 1 | .margin => 2

def fiberBudgetRoleCheck (id : FiberBudgetIdentity) : FiberBudgetRole → Bool
  | .budget => lowMeanIntegerEqualityCheck (fiberBudgetExpr id .budget)
      (fiberBudgetShape id .budget) (fiberBudgetById id).actual_B
  | .strictGap => lowMeanIntegerPositiveCheck (fiberBudgetExpr id .strictGap)
      (fiberBudgetShape id .strictGap) (0,1)
  | .margin => lowMeanIntegerLowerCheck (fiberBudgetExpr id .margin)
      (fiberBudgetShape id .margin) (1,500)

def fiberBudgetParameterTests (id : FiberBudgetIdentity) : Prop :=
  let r := fiberBudgetById id
  r.printed = fiberBudgetPrinted id ∧ r.inputLo ≤ r.inputHi ∧
  lowMeanFractionValid r.mu_star ∧ lowMeanFractionValid r.b ∧ lowMeanFractionValid r.Theta ∧
  lowMeanFractionValid r.D_star ∧ lowMeanFractionValid r.R ∧ lowMeanFractionValid r.B_star ∧
  lowMeanFractionValid r.Z ∧ lowMeanFractionValid r.printed_gap ∧ lowMeanFractionValid r.actual_B ∧
  lowMeanFractionLT (0,1) r.mu_star ∧ lowMeanFractionLE (0,1) r.R ∧ lowMeanFractionLT r.R (1,1) ∧
  lowMeanFractionLE (0,1) r.D_star ∧ lowMeanFractionLE (0,1) r.Theta ∧
  lowMeanFractionEq r.printed_gap (fiberFractionSub r.B_star r.Z)

instance fiberBudgetParameterTestsDecidable (id : FiberBudgetIdentity) :
    Decidable (fiberBudgetParameterTests id) := by unfold fiberBudgetParameterTests; infer_instance

def fiberBudgetCheck (id : FiberBudgetIdentity) (role : FiberBudgetRole) : Bool :=
  decide (fiberBudgetParameterTests id) && fiberBudgetRoleCheck id role

theorem fiber_budget_first_checks :
    (List.range 21).all (fun k => fiberBudgetCheck (fiberBudgetIdentityAt (k/3)) (fiberBudgetRoleAt (k%3))) = true := by
  decide +kernel

theorem fiber_budget_first_checked (id : FiberBudgetIdentity) (role : FiberBudgetRole)
    (hid : fiberBudgetIndex id < 7) : fiberBudgetCheck id role = true := by
  let k := fiberBudgetIndex id*3+fiberBudgetRoleIndex role
  have hk : k < 21 := by cases role <;> simp only [k,fiberBudgetRoleIndex] <;> omega
  have hi : fiberBudgetIdentityAt (k/3) = id ∧ fiberBudgetRoleAt (k%3) = role := by
    cases id <;> cases role <;>
      norm_num [k,fiberBudgetIndex,fiberBudgetRoleIndex,fiberBudgetIdentityAt,fiberBudgetRoleAt]
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_budget_first_checks k hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_budget_first_parameters (id : FiberBudgetIdentity) (hid : fiberBudgetIndex id < 7) :
    fiberBudgetParameterTests id := by
  have h := fiber_budget_first_checked id .budget hid
  simp only [fiberBudgetCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem fiber_budget_first_value (id : FiberBudgetIdentity) (hid : fiberBudgetIndex id < 7) :
    fiberBlockBudget id = lowMeanFractionReal (fiberBudgetById id).actual_B := by
  have h := fiber_budget_first_checked id .budget hid
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerEquality_sound h.2
  rw [fiber_budget_shape_real] at hv
  exact hv

theorem fiber_budget_first_strict (id : FiberBudgetIdentity) (hid : fiberBudgetIndex id < 7) :
    lowMeanFractionReal (fiberBudgetById id).B_star < fiberBlockBudget id := by
  have h := fiber_budget_first_checked id .strictGap hid
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerPositive_sound h.2
  rw [fiber_budget_shape_real] at hv
  norm_num only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] at hv
  change 0 < fiberBlockBudget id-lowMeanFractionReal (fiberBudgetById id).B_star at hv
  linarith only [hv]

theorem fiber_budget_first_margin (id : FiberBudgetIdentity) (hid : fiberBudgetIndex id < 7) :
    (1/500 : ℝ) ≤ lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z := by
  have h := fiber_budget_first_checked id .margin hid
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerLower_sound h.2
  rw [fiber_budget_shape_real] at hv
  norm_num only [lowMeanFractionReal,Int.cast_one,Nat.cast_ofNat] at hv
  exact hv

theorem fiber_budget_first_seven (id : FiberBudgetIdentity) (hid : fiberBudgetIndex id < 7) :
    lowMeanFractionReal (fiberBudgetById id).B_star < fiberBlockBudget id ∧
    (1/500 : ℝ) ≤ lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z ∧
    lowMeanFractionReal (fiberBudgetById id).printed_gap =
      lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z := by
  refine ⟨fiber_budget_first_strict id hid,fiber_budget_first_margin id hid,?_⟩
  have h := fiber_budget_first_parameters id hid
  rcases h with ⟨_,_,_,_,_,_,_,hb,hz,hgap,_,_,_,_,_,_,he⟩
  have hv := (lowMean_fraction_eq_iff hgap (fiber_fraction_sub_valid hb hz)).mp he
  rw [fiber_fraction_sub_real hb hz] at hv
  exact hv

end Erdos993Lean.Analytic.V213
