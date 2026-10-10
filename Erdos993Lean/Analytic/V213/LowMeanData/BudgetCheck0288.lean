module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0288
public import Erdos993Lean.Analytic.V213.LowMeanData.BudgetCheck0208
public import Erdos993Lean.LowMeanFast.FastBudget

/-! Frozen budget records 288--303. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budgetGroup0288_kernel : lowMeanBudgetGroup0288.all lowMeanBudgetFamilyCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastBudgetGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetGroup0288_kernel
