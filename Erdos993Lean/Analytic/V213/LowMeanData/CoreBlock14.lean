module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0557
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0559
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0561
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0563
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0553
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0557
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0559
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0561
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0563

/-! Complete frozen core block 14, fibers 557--563. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock14 : List LowMeanFiberInput :=
  lowMeanFiberGroup0557 ++ lowMeanFiberGroup0559 ++ lowMeanFiberGroup0561 ++ lowMeanFiberGroup0563

theorem lowMeanCoreBlock14_kernel : lowMeanCoreBlock14.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock14, List.all_append, lowMean_fiberGroup0557_kernel, lowMean_fiberGroup0559_kernel, lowMean_fiberGroup0561_kernel, lowMean_fiberGroup0563_kernel, Bool.and_self]

theorem lowMeanCoreBlock14_length : lowMeanCoreBlock14.length = 7 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
