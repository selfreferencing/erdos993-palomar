module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0279
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0281
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0283
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0285
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0287
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0289
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0291
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0293
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0295
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0297
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0299
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0301
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0303
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0305
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0307
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0309
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0311
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0313
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0315
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0317
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0279
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0281
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0283
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0285
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0287
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0289
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0291
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0293
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0295
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0297
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0299
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0301
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0303
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0305
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0307
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0309
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0311
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0313
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0315
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0317

/-! Complete frozen core block 7, fibers 279--318. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock07 : List LowMeanFiberInput :=
  lowMeanFiberGroup0279 ++ lowMeanFiberGroup0281 ++ lowMeanFiberGroup0283 ++ lowMeanFiberGroup0285 ++ lowMeanFiberGroup0287 ++ lowMeanFiberGroup0289 ++ lowMeanFiberGroup0291 ++ lowMeanFiberGroup0293 ++ lowMeanFiberGroup0295 ++ lowMeanFiberGroup0297 ++ lowMeanFiberGroup0299 ++ lowMeanFiberGroup0301 ++ lowMeanFiberGroup0303 ++ lowMeanFiberGroup0305 ++ lowMeanFiberGroup0307 ++ lowMeanFiberGroup0309 ++ lowMeanFiberGroup0311 ++ lowMeanFiberGroup0313 ++ lowMeanFiberGroup0315 ++ lowMeanFiberGroup0317

theorem lowMeanCoreBlock07_kernel : lowMeanCoreBlock07.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock07, List.all_append, lowMean_fiberGroup0279_kernel, lowMean_fiberGroup0281_kernel, lowMean_fiberGroup0283_kernel, lowMean_fiberGroup0285_kernel, lowMean_fiberGroup0287_kernel, lowMean_fiberGroup0289_kernel, lowMean_fiberGroup0291_kernel, lowMean_fiberGroup0293_kernel, lowMean_fiberGroup0295_kernel, lowMean_fiberGroup0297_kernel, lowMean_fiberGroup0299_kernel, lowMean_fiberGroup0301_kernel, lowMean_fiberGroup0303_kernel, lowMean_fiberGroup0305_kernel, lowMean_fiberGroup0307_kernel, lowMean_fiberGroup0309_kernel, lowMean_fiberGroup0311_kernel, lowMean_fiberGroup0313_kernel, lowMean_fiberGroup0315_kernel, lowMean_fiberGroup0317_kernel, Bool.and_self]

theorem lowMeanCoreBlock07_length : lowMeanCoreBlock07.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
