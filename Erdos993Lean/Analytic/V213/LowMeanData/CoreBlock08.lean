module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0319
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0321
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0323
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0325
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0327
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0329
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0331
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0333
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0335
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0337
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0339
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0341
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0343
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0345
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0347
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0349
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0351
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0353
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0355
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0357
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0319
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0321
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0323
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0325
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0327
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0329
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0331
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0333
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0335
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0337
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0339
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0341
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0343
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0345
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0347
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0349
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0351
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0353
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0355
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0357

/-! Complete frozen core block 8, fibers 319--358. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock08 : List LowMeanFiberInput :=
  lowMeanFiberGroup0319 ++ lowMeanFiberGroup0321 ++ lowMeanFiberGroup0323 ++ lowMeanFiberGroup0325 ++ lowMeanFiberGroup0327 ++ lowMeanFiberGroup0329 ++ lowMeanFiberGroup0331 ++ lowMeanFiberGroup0333 ++ lowMeanFiberGroup0335 ++ lowMeanFiberGroup0337 ++ lowMeanFiberGroup0339 ++ lowMeanFiberGroup0341 ++ lowMeanFiberGroup0343 ++ lowMeanFiberGroup0345 ++ lowMeanFiberGroup0347 ++ lowMeanFiberGroup0349 ++ lowMeanFiberGroup0351 ++ lowMeanFiberGroup0353 ++ lowMeanFiberGroup0355 ++ lowMeanFiberGroup0357

theorem lowMeanCoreBlock08_kernel : lowMeanCoreBlock08.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock08, List.all_append, lowMean_fiberGroup0319_kernel, lowMean_fiberGroup0321_kernel, lowMean_fiberGroup0323_kernel, lowMean_fiberGroup0325_kernel, lowMean_fiberGroup0327_kernel, lowMean_fiberGroup0329_kernel, lowMean_fiberGroup0331_kernel, lowMean_fiberGroup0333_kernel, lowMean_fiberGroup0335_kernel, lowMean_fiberGroup0337_kernel, lowMean_fiberGroup0339_kernel, lowMean_fiberGroup0341_kernel, lowMean_fiberGroup0343_kernel, lowMean_fiberGroup0345_kernel, lowMean_fiberGroup0347_kernel, lowMean_fiberGroup0349_kernel, lowMean_fiberGroup0351_kernel, lowMean_fiberGroup0353_kernel, lowMean_fiberGroup0355_kernel, lowMean_fiberGroup0357_kernel, Bool.and_self]

theorem lowMeanCoreBlock08_length : lowMeanCoreBlock08.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
