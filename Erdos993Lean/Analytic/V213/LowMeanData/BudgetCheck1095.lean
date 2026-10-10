module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget1095
public import Erdos993Lean.Analytic.V213.LowMeanData.BudgetCheck1015
public import Erdos993Lean.LowMeanFast.FastBudget

/-! Frozen budget records 1095--1110. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budgetGroup1095_kernel : lowMeanBudgetGroup1095.all lowMeanBudgetFamilyCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastBudgetGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetGroup1095_kernel
