module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0039
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0041
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0043
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0045
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0047
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0049
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0051
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0053
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0055
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0057
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0059
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0061
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0063
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0065
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0067
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0069
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0071
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0073
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0075
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0077
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0039
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0041
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0043
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0045
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0047
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0049
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0051
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0053
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0055
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0057
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0059
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0061
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0063
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0065
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0067
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0069
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0071
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0073
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0075
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0077

/-! Complete frozen core block 1, fibers 39--78. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock01 : List LowMeanFiberInput :=
  lowMeanFiberGroup0039 ++ lowMeanFiberGroup0041 ++ lowMeanFiberGroup0043 ++ lowMeanFiberGroup0045 ++ lowMeanFiberGroup0047 ++ lowMeanFiberGroup0049 ++ lowMeanFiberGroup0051 ++ lowMeanFiberGroup0053 ++ lowMeanFiberGroup0055 ++ lowMeanFiberGroup0057 ++ lowMeanFiberGroup0059 ++ lowMeanFiberGroup0061 ++ lowMeanFiberGroup0063 ++ lowMeanFiberGroup0065 ++ lowMeanFiberGroup0067 ++ lowMeanFiberGroup0069 ++ lowMeanFiberGroup0071 ++ lowMeanFiberGroup0073 ++ lowMeanFiberGroup0075 ++ lowMeanFiberGroup0077

theorem lowMeanCoreBlock01_kernel : lowMeanCoreBlock01.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock01, List.all_append, lowMean_fiberGroup0039_kernel, lowMean_fiberGroup0041_kernel, lowMean_fiberGroup0043_kernel, lowMean_fiberGroup0045_kernel, lowMean_fiberGroup0047_kernel, lowMean_fiberGroup0049_kernel, lowMean_fiberGroup0051_kernel, lowMean_fiberGroup0053_kernel, lowMean_fiberGroup0055_kernel, lowMean_fiberGroup0057_kernel, lowMean_fiberGroup0059_kernel, lowMean_fiberGroup0061_kernel, lowMean_fiberGroup0063_kernel, lowMean_fiberGroup0065_kernel, lowMean_fiberGroup0067_kernel, lowMean_fiberGroup0069_kernel, lowMean_fiberGroup0071_kernel, lowMean_fiberGroup0073_kernel, lowMean_fiberGroup0075_kernel, lowMean_fiberGroup0077_kernel, Bool.and_self]

theorem lowMeanCoreBlock01_length : lowMeanCoreBlock01.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
