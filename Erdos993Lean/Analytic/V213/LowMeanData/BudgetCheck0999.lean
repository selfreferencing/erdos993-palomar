module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0999
public import Erdos993Lean.Analytic.V213.LowMeanData.BudgetCheck0887
public import Erdos993Lean.LowMeanFast.FastBudget

/-! Frozen budget records 999--1014. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budgetGroup0999_kernel : lowMeanBudgetGroup0999.all lowMeanBudgetFamilyCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastBudgetGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetGroup0999_kernel
