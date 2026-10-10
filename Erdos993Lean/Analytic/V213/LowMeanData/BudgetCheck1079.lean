module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget1079
public import Erdos993Lean.Analytic.V213.LowMeanData.BudgetCheck0983
public import Erdos993Lean.LowMeanFast.FastBudget

/-! Frozen budget records 1079--1094. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budgetGroup1079_kernel : lowMeanBudgetGroup1079.all lowMeanBudgetFamilyCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastBudgetGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetGroup1079_kernel
