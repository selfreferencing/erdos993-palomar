module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0000
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0003
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0005
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0007
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0009
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0011
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0013
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0015
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0017
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0019
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0021
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0023
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0025
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0027
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0029
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0031Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0033Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0035
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0037
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0000
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0001
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0003
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0005
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0007
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0009
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0011
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0013
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0015
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0017
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0019
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0021
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0023
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0025
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0027
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0029
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0031
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0033
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0035
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0037

/-! Complete frozen core block 0, fibers 0--38. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock00 : List LowMeanFiberInput :=
  lowMeanFiberGroup0000 ++ lowMeanFiberGroup0001 ++ lowMeanFiberGroup0003 ++ lowMeanFiberGroup0005 ++ lowMeanFiberGroup0007 ++ lowMeanFiberGroup0009 ++ lowMeanFiberGroup0011 ++ lowMeanFiberGroup0013 ++ lowMeanFiberGroup0015 ++ lowMeanFiberGroup0017 ++ lowMeanFiberGroup0019 ++ lowMeanFiberGroup0021 ++ lowMeanFiberGroup0023 ++ lowMeanFiberGroup0025 ++ lowMeanFiberGroup0027 ++ lowMeanFiberGroup0029 ++ lowMeanFiberGroup0031 ++ lowMeanFiberGroup0033 ++ lowMeanFiberGroup0035 ++ lowMeanFiberGroup0037

theorem lowMeanCoreBlock00_kernel : lowMeanCoreBlock00.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock00, List.all_append, lowMean_fiberGroup0000_kernel, lowMean_fiberGroup0001_kernel, lowMean_fiberGroup0003_kernel, lowMean_fiberGroup0005_kernel, lowMean_fiberGroup0007_kernel, lowMean_fiberGroup0009_kernel, lowMean_fiberGroup0011_kernel, lowMean_fiberGroup0013_kernel, lowMean_fiberGroup0015_kernel, lowMean_fiberGroup0017_kernel, lowMean_fiberGroup0019_kernel, lowMean_fiberGroup0021_kernel, lowMean_fiberGroup0023_kernel, lowMean_fiberGroup0025_kernel, lowMean_fiberGroup0027_kernel, lowMean_fiberGroup0029_kernel, lowMean_fiberGroup0031_kernel, lowMean_fiberGroup0033_kernel, lowMean_fiberGroup0035_kernel, lowMean_fiberGroup0037_kernel, Bool.and_self]

theorem lowMeanCoreBlock00_length : lowMeanCoreBlock00.length = 39 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
