module

public import Erdos993Lean.Analytic.V213.FiberBudgetFirstCheck

/-!
Remaining six printed F17 budgets, following the first seven
rows. The same complete canonical Int/Nat checker is used; no
new numerical table or weakened margin is introduced.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_budget_rest_checks :
    (List.range 18).all (fun k => fiberBudgetCheck (fiberBudgetIdentityAt (7+k/3)) (fiberBudgetRoleAt (k%3))) = true := by
  decide +kernel

theorem fiber_budget_rest_checked (id : FiberBudgetIdentity) (role : FiberBudgetRole)
    (hid : 7 ≤ fiberBudgetIndex id) : fiberBudgetCheck id role = true := by
  let k := (fiberBudgetIndex id-7)*3+fiberBudgetRoleIndex role
  have hi13 : fiberBudgetIndex id < 13 := by cases id <;> decide +kernel
  have hk : k < 18 := by cases role <;> simp only [k,fiberBudgetRoleIndex] <;> omega
  have hi : fiberBudgetIdentityAt (7+k/3) = id ∧ fiberBudgetRoleAt (k%3) = role := by
    cases id <;> cases role <;>
      norm_num [fiberBudgetIndex] at hid <;>
      norm_num [k,fiberBudgetIndex,fiberBudgetRoleIndex,fiberBudgetIdentityAt,fiberBudgetRoleAt]
  have h := Erdos993Lean.F4Fast.forall_lt_of_range_all fiber_budget_rest_checks k hk
  rw [hi.1,hi.2] at h
  exact h

theorem fiber_budget_checked (id : FiberBudgetIdentity) (role : FiberBudgetRole) :
    fiberBudgetCheck id role = true := by
  by_cases hid : fiberBudgetIndex id < 7
  · exact fiber_budget_first_checked id role hid
  · exact fiber_budget_rest_checked id role (by omega)

theorem fiber_budget_parameters (id : FiberBudgetIdentity) : fiberBudgetParameterTests id := by
  have h := fiber_budget_checked id .budget
  simp only [fiberBudgetCheck,Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem fiber_budget_value (id : FiberBudgetIdentity) :
    fiberBlockBudget id = lowMeanFractionReal (fiberBudgetById id).actual_B := by
  have h := fiber_budget_checked id .budget
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerEquality_sound h.2
  rw [fiber_budget_shape_real] at hv
  exact hv

theorem fiber_budget_strict (id : FiberBudgetIdentity) :
    lowMeanFractionReal (fiberBudgetById id).B_star < fiberBlockBudget id := by
  have h := fiber_budget_checked id .strictGap
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerPositive_sound h.2
  rw [fiber_budget_shape_real] at hv
  norm_num only [lowMeanFractionReal,Int.cast_zero,Nat.cast_one,zero_div] at hv
  change 0 < fiberBlockBudget id-lowMeanFractionReal (fiberBudgetById id).B_star at hv
  linarith only [hv]

theorem fiber_budget_margin (id : FiberBudgetIdentity) :
    (1/500 : ℝ) ≤ lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z := by
  have h := fiber_budget_checked id .margin
  simp only [fiberBudgetCheck,Bool.and_eq_true,fiberBudgetRoleCheck] at h
  have hv := lowMean_integerLower_sound h.2
  rw [fiber_budget_shape_real] at hv
  norm_num only [lowMeanFractionReal,Int.cast_one,Nat.cast_ofNat] at hv
  exact hv

theorem fiber_budget_all_thirteen (id : FiberBudgetIdentity) :
    lowMeanFractionReal (fiberBudgetById id).B_star < fiberBlockBudget id ∧
    (1/500 : ℝ) ≤ lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z ∧
    lowMeanFractionReal (fiberBudgetById id).printed_gap =
      lowMeanFractionReal (fiberBudgetById id).B_star-lowMeanFractionReal (fiberBudgetById id).Z := by
  refine ⟨fiber_budget_strict id,fiber_budget_margin id,?_⟩
  rcases fiber_budget_parameters id with ⟨_,_,_,_,_,_,_,hb,hz,hgap,_,_,_,_,_,_,he⟩
  have hv := (lowMean_fraction_eq_iff hgap (fiber_fraction_sub_valid hb hz)).mp he
  rw [fiber_fraction_sub_real hb hz] at hv
  exact hv

end Erdos993Lean.Analytic.V213
