module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0359
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0361
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0363
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0365
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0367
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0369
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0371
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0373
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0375
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0377
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0379
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0381
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0383
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0385
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0387
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0389
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0391
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0393
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0395
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0397
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0359
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0361
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0363
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0365
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0367
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0369
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0371
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0373
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0375
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0377
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0379
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0381
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0383
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0385
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0387
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0389
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0391
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0393
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0395
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0397

/-! Complete frozen core block 9, fibers 359--398. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock09 : List LowMeanFiberInput :=
  lowMeanFiberGroup0359 ++ lowMeanFiberGroup0361 ++ lowMeanFiberGroup0363 ++ lowMeanFiberGroup0365 ++ lowMeanFiberGroup0367 ++ lowMeanFiberGroup0369 ++ lowMeanFiberGroup0371 ++ lowMeanFiberGroup0373 ++ lowMeanFiberGroup0375 ++ lowMeanFiberGroup0377 ++ lowMeanFiberGroup0379 ++ lowMeanFiberGroup0381 ++ lowMeanFiberGroup0383 ++ lowMeanFiberGroup0385 ++ lowMeanFiberGroup0387 ++ lowMeanFiberGroup0389 ++ lowMeanFiberGroup0391 ++ lowMeanFiberGroup0393 ++ lowMeanFiberGroup0395 ++ lowMeanFiberGroup0397

theorem lowMeanCoreBlock09_kernel : lowMeanCoreBlock09.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock09, List.all_append, lowMean_fiberGroup0359_kernel, lowMean_fiberGroup0361_kernel, lowMean_fiberGroup0363_kernel, lowMean_fiberGroup0365_kernel, lowMean_fiberGroup0367_kernel, lowMean_fiberGroup0369_kernel, lowMean_fiberGroup0371_kernel, lowMean_fiberGroup0373_kernel, lowMean_fiberGroup0375_kernel, lowMean_fiberGroup0377_kernel, lowMean_fiberGroup0379_kernel, lowMean_fiberGroup0381_kernel, lowMean_fiberGroup0383_kernel, lowMean_fiberGroup0385_kernel, lowMean_fiberGroup0387_kernel, lowMean_fiberGroup0389_kernel, lowMean_fiberGroup0391_kernel, lowMean_fiberGroup0393_kernel, lowMean_fiberGroup0395_kernel, lowMean_fiberGroup0397_kernel, Bool.and_self]

theorem lowMeanCoreBlock09_length : lowMeanCoreBlock09.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
