module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0497Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0489
public import Erdos993Lean.LowMeanFast.FastCheck

/-! Exact complete core checks for frozen fibers 497--498. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_fiberGroup0497_kernel : lowMeanFiberGroup0497.all lowMeanFiberCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fiberGroup0497_kernel
