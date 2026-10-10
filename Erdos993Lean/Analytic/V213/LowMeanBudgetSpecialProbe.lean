module

public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0000
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0016
public import Erdos993Lean.Analytic.V213.LowMeanData.Budget0032

/-! All seven printed additional anchors, exact unreduced printed floors. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_budget_special_probe_kernel :
    [lowMeanBudgetRecord0014, lowMeanBudgetRecord0020, lowMeanBudgetRecord0021,
      lowMeanBudgetRecord0030, lowMeanBudgetRecord0031, lowMeanBudgetRecord0038,
      lowMeanBudgetRecord0042].all lowMeanBudgetFamilyCheck = true := by
  decide +kernel

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_budget_special_probe_kernel
