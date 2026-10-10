module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0079
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0081
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0083
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0085
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0087
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0089
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0091
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0093
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0095
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0097
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0099
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0101
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0103
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0105
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0107
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0109
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0111
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0113
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0115
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0117
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0079
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0081
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0083
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0085
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0087
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0089
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0091
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0093
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0095
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0097
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0099
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0101
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0103
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0105
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0107
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0109
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0111
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0113
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0115
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0117

/-! Complete frozen core block 2, fibers 79--118. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock02 : List LowMeanFiberInput :=
  lowMeanFiberGroup0079 ++ lowMeanFiberGroup0081 ++ lowMeanFiberGroup0083 ++ lowMeanFiberGroup0085 ++ lowMeanFiberGroup0087 ++ lowMeanFiberGroup0089 ++ lowMeanFiberGroup0091 ++ lowMeanFiberGroup0093 ++ lowMeanFiberGroup0095 ++ lowMeanFiberGroup0097 ++ lowMeanFiberGroup0099 ++ lowMeanFiberGroup0101 ++ lowMeanFiberGroup0103 ++ lowMeanFiberGroup0105 ++ lowMeanFiberGroup0107 ++ lowMeanFiberGroup0109 ++ lowMeanFiberGroup0111 ++ lowMeanFiberGroup0113 ++ lowMeanFiberGroup0115 ++ lowMeanFiberGroup0117

theorem lowMeanCoreBlock02_kernel : lowMeanCoreBlock02.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock02, List.all_append, lowMean_fiberGroup0079_kernel, lowMean_fiberGroup0081_kernel, lowMean_fiberGroup0083_kernel, lowMean_fiberGroup0085_kernel, lowMean_fiberGroup0087_kernel, lowMean_fiberGroup0089_kernel, lowMean_fiberGroup0091_kernel, lowMean_fiberGroup0093_kernel, lowMean_fiberGroup0095_kernel, lowMean_fiberGroup0097_kernel, lowMean_fiberGroup0099_kernel, lowMean_fiberGroup0101_kernel, lowMean_fiberGroup0103_kernel, lowMean_fiberGroup0105_kernel, lowMean_fiberGroup0107_kernel, lowMean_fiberGroup0109_kernel, lowMean_fiberGroup0111_kernel, lowMean_fiberGroup0113_kernel, lowMean_fiberGroup0115_kernel, lowMean_fiberGroup0117_kernel, Bool.and_self]

theorem lowMeanCoreBlock02_length : lowMeanCoreBlock02.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
