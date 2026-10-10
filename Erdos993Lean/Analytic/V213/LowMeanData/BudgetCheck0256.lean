module

public import Erdos993Lean.Analytic.V213.LowMeanBudgetFamily
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0256
public import Erdos993Lean.Analytic.V213.LowMeanData.BudgetCheck0192
public import Erdos993Lean.LowMeanFast.FastBudget

/-! Frozen budget records 256--271. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budgetGroup0256_kernel : lowMeanBudgetGroup0256.all lowMeanBudgetFamilyCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastBudgetGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budgetGroup0256_kernel
