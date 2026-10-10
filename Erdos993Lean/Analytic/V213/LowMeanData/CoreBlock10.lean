module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0399
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0401
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0403
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0405
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0407
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0409
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0411
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0413
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0415
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0417
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0419
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0421
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0423
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0425
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0427
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0429
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0431
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0433
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0435
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0437
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0399
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0401
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0403
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0405
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0407
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0409
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0411
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0413
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0415
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0417
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0419
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0421
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0423
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0425
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0427
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0429
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0431
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0433
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0435
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0437

/-! Complete frozen core block 10, fibers 399--438. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock10 : List LowMeanFiberInput :=
  lowMeanFiberGroup0399 ++ lowMeanFiberGroup0401 ++ lowMeanFiberGroup0403 ++ lowMeanFiberGroup0405 ++ lowMeanFiberGroup0407 ++ lowMeanFiberGroup0409 ++ lowMeanFiberGroup0411 ++ lowMeanFiberGroup0413 ++ lowMeanFiberGroup0415 ++ lowMeanFiberGroup0417 ++ lowMeanFiberGroup0419 ++ lowMeanFiberGroup0421 ++ lowMeanFiberGroup0423 ++ lowMeanFiberGroup0425 ++ lowMeanFiberGroup0427 ++ lowMeanFiberGroup0429 ++ lowMeanFiberGroup0431 ++ lowMeanFiberGroup0433 ++ lowMeanFiberGroup0435 ++ lowMeanFiberGroup0437

theorem lowMeanCoreBlock10_kernel : lowMeanCoreBlock10.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock10, List.all_append, lowMean_fiberGroup0399_kernel, lowMean_fiberGroup0401_kernel, lowMean_fiberGroup0403_kernel, lowMean_fiberGroup0405_kernel, lowMean_fiberGroup0407_kernel, lowMean_fiberGroup0409_kernel, lowMean_fiberGroup0411_kernel, lowMean_fiberGroup0413_kernel, lowMean_fiberGroup0415_kernel, lowMean_fiberGroup0417_kernel, lowMean_fiberGroup0419_kernel, lowMean_fiberGroup0421_kernel, lowMean_fiberGroup0423_kernel, lowMean_fiberGroup0425_kernel, lowMean_fiberGroup0427_kernel, lowMean_fiberGroup0429_kernel, lowMean_fiberGroup0431_kernel, lowMean_fiberGroup0433_kernel, lowMean_fiberGroup0435_kernel, lowMean_fiberGroup0437_kernel, Bool.and_self]

theorem lowMeanCoreBlock10_length : lowMeanCoreBlock10.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
