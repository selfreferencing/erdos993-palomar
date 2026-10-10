module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0239
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0241
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0243
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0245
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0247
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0249
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0251
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0253
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0255
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0257
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0259
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0261
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0263
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0265
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0267
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0269
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0271
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0273
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0275
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0277
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0239
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0241
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0243
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0245
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0247
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0249
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0251
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0253
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0255
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0257
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0259
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0261
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0263
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0265
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0267
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0269
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0271
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0273
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0275
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0277

/-! Complete frozen core block 6, fibers 239--278. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock06 : List LowMeanFiberInput :=
  lowMeanFiberGroup0239 ++ lowMeanFiberGroup0241 ++ lowMeanFiberGroup0243 ++ lowMeanFiberGroup0245 ++ lowMeanFiberGroup0247 ++ lowMeanFiberGroup0249 ++ lowMeanFiberGroup0251 ++ lowMeanFiberGroup0253 ++ lowMeanFiberGroup0255 ++ lowMeanFiberGroup0257 ++ lowMeanFiberGroup0259 ++ lowMeanFiberGroup0261 ++ lowMeanFiberGroup0263 ++ lowMeanFiberGroup0265 ++ lowMeanFiberGroup0267 ++ lowMeanFiberGroup0269 ++ lowMeanFiberGroup0271 ++ lowMeanFiberGroup0273 ++ lowMeanFiberGroup0275 ++ lowMeanFiberGroup0277

theorem lowMeanCoreBlock06_kernel : lowMeanCoreBlock06.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock06, List.all_append, lowMean_fiberGroup0239_kernel, lowMean_fiberGroup0241_kernel, lowMean_fiberGroup0243_kernel, lowMean_fiberGroup0245_kernel, lowMean_fiberGroup0247_kernel, lowMean_fiberGroup0249_kernel, lowMean_fiberGroup0251_kernel, lowMean_fiberGroup0253_kernel, lowMean_fiberGroup0255_kernel, lowMean_fiberGroup0257_kernel, lowMean_fiberGroup0259_kernel, lowMean_fiberGroup0261_kernel, lowMean_fiberGroup0263_kernel, lowMean_fiberGroup0265_kernel, lowMean_fiberGroup0267_kernel, lowMean_fiberGroup0269_kernel, lowMean_fiberGroup0271_kernel, lowMean_fiberGroup0273_kernel, lowMean_fiberGroup0275_kernel, lowMean_fiberGroup0277_kernel, Bool.and_self]

theorem lowMeanCoreBlock06_length : lowMeanCoreBlock06.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
