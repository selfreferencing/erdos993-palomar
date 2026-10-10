module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0119
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0121
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0123
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0125
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0127
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0129
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0131
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0133
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0135
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0137
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0139
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0141
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0143
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0145
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0147
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0149
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0151
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0153
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0155
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0157
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0119
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0121
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0123
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0125
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0127
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0129
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0131
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0133
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0135
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0137
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0139
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0141
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0143
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0145
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0147
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0149
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0151
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0153
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0155
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0157

/-! Complete frozen core block 3, fibers 119--158. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock03 : List LowMeanFiberInput :=
  lowMeanFiberGroup0119 ++ lowMeanFiberGroup0121 ++ lowMeanFiberGroup0123 ++ lowMeanFiberGroup0125 ++ lowMeanFiberGroup0127 ++ lowMeanFiberGroup0129 ++ lowMeanFiberGroup0131 ++ lowMeanFiberGroup0133 ++ lowMeanFiberGroup0135 ++ lowMeanFiberGroup0137 ++ lowMeanFiberGroup0139 ++ lowMeanFiberGroup0141 ++ lowMeanFiberGroup0143 ++ lowMeanFiberGroup0145 ++ lowMeanFiberGroup0147 ++ lowMeanFiberGroup0149 ++ lowMeanFiberGroup0151 ++ lowMeanFiberGroup0153 ++ lowMeanFiberGroup0155 ++ lowMeanFiberGroup0157

theorem lowMeanCoreBlock03_kernel : lowMeanCoreBlock03.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock03, List.all_append, lowMean_fiberGroup0119_kernel, lowMean_fiberGroup0121_kernel, lowMean_fiberGroup0123_kernel, lowMean_fiberGroup0125_kernel, lowMean_fiberGroup0127_kernel, lowMean_fiberGroup0129_kernel, lowMean_fiberGroup0131_kernel, lowMean_fiberGroup0133_kernel, lowMean_fiberGroup0135_kernel, lowMean_fiberGroup0137_kernel, lowMean_fiberGroup0139_kernel, lowMean_fiberGroup0141_kernel, lowMean_fiberGroup0143_kernel, lowMean_fiberGroup0145_kernel, lowMean_fiberGroup0147_kernel, lowMean_fiberGroup0149_kernel, lowMean_fiberGroup0151_kernel, lowMean_fiberGroup0153_kernel, lowMean_fiberGroup0155_kernel, lowMean_fiberGroup0157_kernel, Bool.and_self]

theorem lowMeanCoreBlock03_length : lowMeanCoreBlock03.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
