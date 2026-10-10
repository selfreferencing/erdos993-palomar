module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0439
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0441
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0443
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0445
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0447
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0449
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0451
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0453
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0455
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0457
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0459
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0461
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0463
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0465
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0467
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0469
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0471
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0473
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0475
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0477
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0439
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0441
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0443
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0445
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0447
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0449
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0451
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0453
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0455
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0457
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0459
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0461
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0463
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0465
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0467
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0469
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0471
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0473
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0475
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0477

/-! Complete frozen core block 11, fibers 439--478. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock11 : List LowMeanFiberInput :=
  lowMeanFiberGroup0439 ++ lowMeanFiberGroup0441 ++ lowMeanFiberGroup0443 ++ lowMeanFiberGroup0445 ++ lowMeanFiberGroup0447 ++ lowMeanFiberGroup0449 ++ lowMeanFiberGroup0451 ++ lowMeanFiberGroup0453 ++ lowMeanFiberGroup0455 ++ lowMeanFiberGroup0457 ++ lowMeanFiberGroup0459 ++ lowMeanFiberGroup0461 ++ lowMeanFiberGroup0463 ++ lowMeanFiberGroup0465 ++ lowMeanFiberGroup0467 ++ lowMeanFiberGroup0469 ++ lowMeanFiberGroup0471 ++ lowMeanFiberGroup0473 ++ lowMeanFiberGroup0475 ++ lowMeanFiberGroup0477

theorem lowMeanCoreBlock11_kernel : lowMeanCoreBlock11.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock11, List.all_append, lowMean_fiberGroup0439_kernel, lowMean_fiberGroup0441_kernel, lowMean_fiberGroup0443_kernel, lowMean_fiberGroup0445_kernel, lowMean_fiberGroup0447_kernel, lowMean_fiberGroup0449_kernel, lowMean_fiberGroup0451_kernel, lowMean_fiberGroup0453_kernel, lowMean_fiberGroup0455_kernel, lowMean_fiberGroup0457_kernel, lowMean_fiberGroup0459_kernel, lowMean_fiberGroup0461_kernel, lowMean_fiberGroup0463_kernel, lowMean_fiberGroup0465_kernel, lowMean_fiberGroup0467_kernel, lowMean_fiberGroup0469_kernel, lowMean_fiberGroup0471_kernel, lowMean_fiberGroup0473_kernel, lowMean_fiberGroup0475_kernel, lowMean_fiberGroup0477_kernel, Bool.and_self]

theorem lowMeanCoreBlock11_length : lowMeanCoreBlock11.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
