module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0199
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0201
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0203
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0205
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0207
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0209
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0211
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0213
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0215
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0217
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0219
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0221
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0223
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0225
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0227
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0229
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0231
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0233
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0235
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0237
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0199
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0201
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0203
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0205
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0207
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0209
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0211
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0213
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0215
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0217
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0219
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0221
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0223
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0225
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0227
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0229
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0231
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0233
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0235
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0237

/-! Complete frozen core block 5, fibers 199--238. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock05 : List LowMeanFiberInput :=
  lowMeanFiberGroup0199 ++ lowMeanFiberGroup0201 ++ lowMeanFiberGroup0203 ++ lowMeanFiberGroup0205 ++ lowMeanFiberGroup0207 ++ lowMeanFiberGroup0209 ++ lowMeanFiberGroup0211 ++ lowMeanFiberGroup0213 ++ lowMeanFiberGroup0215 ++ lowMeanFiberGroup0217 ++ lowMeanFiberGroup0219 ++ lowMeanFiberGroup0221 ++ lowMeanFiberGroup0223 ++ lowMeanFiberGroup0225 ++ lowMeanFiberGroup0227 ++ lowMeanFiberGroup0229 ++ lowMeanFiberGroup0231 ++ lowMeanFiberGroup0233 ++ lowMeanFiberGroup0235 ++ lowMeanFiberGroup0237

theorem lowMeanCoreBlock05_kernel : lowMeanCoreBlock05.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock05, List.all_append, lowMean_fiberGroup0199_kernel, lowMean_fiberGroup0201_kernel, lowMean_fiberGroup0203_kernel, lowMean_fiberGroup0205_kernel, lowMean_fiberGroup0207_kernel, lowMean_fiberGroup0209_kernel, lowMean_fiberGroup0211_kernel, lowMean_fiberGroup0213_kernel, lowMean_fiberGroup0215_kernel, lowMean_fiberGroup0217_kernel, lowMean_fiberGroup0219_kernel, lowMean_fiberGroup0221_kernel, lowMean_fiberGroup0223_kernel, lowMean_fiberGroup0225_kernel, lowMean_fiberGroup0227_kernel, lowMean_fiberGroup0229_kernel, lowMean_fiberGroup0231_kernel, lowMean_fiberGroup0233_kernel, lowMean_fiberGroup0235_kernel, lowMean_fiberGroup0237_kernel, Bool.and_self]

theorem lowMeanCoreBlock05_length : lowMeanCoreBlock05.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
