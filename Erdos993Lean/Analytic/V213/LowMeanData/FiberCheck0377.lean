module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0377
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0367
public import Erdos993Lean.LowMeanFast.FastCheck

/-! Exact complete core checks for frozen fibers 377--378. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_fiberGroup0377_kernel : lowMeanFiberGroup0377.all lowMeanFiberCheck = true := by
  exact Erdos993Lean.LowMeanFast.fastGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_fiberGroup0377_kernel
