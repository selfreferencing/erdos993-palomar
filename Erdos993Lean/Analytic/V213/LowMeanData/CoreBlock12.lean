module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0479
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0481
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0483
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0485
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0487Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0489Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0491Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0493Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0495Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0497Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0499Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0501Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0503Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0505Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0507Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0509Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0511Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0513Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0515Part0002
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0517Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0479
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0481
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0483
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0485
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0487
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0489
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0491
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0493
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0495
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0497
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0499
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0501
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0503
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0505
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0507
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0509
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0511
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0513
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0515
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0517

/-! Complete frozen core block 12, fibers 479--517. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock12 : List LowMeanFiberInput :=
  lowMeanFiberGroup0479 ++ lowMeanFiberGroup0481 ++ lowMeanFiberGroup0483 ++ lowMeanFiberGroup0485 ++ lowMeanFiberGroup0487 ++ lowMeanFiberGroup0489 ++ lowMeanFiberGroup0491 ++ lowMeanFiberGroup0493 ++ lowMeanFiberGroup0495 ++ lowMeanFiberGroup0497 ++ lowMeanFiberGroup0499 ++ lowMeanFiberGroup0501 ++ lowMeanFiberGroup0503 ++ lowMeanFiberGroup0505 ++ lowMeanFiberGroup0507 ++ lowMeanFiberGroup0509 ++ lowMeanFiberGroup0511 ++ lowMeanFiberGroup0513 ++ lowMeanFiberGroup0515 ++ lowMeanFiberGroup0517

theorem lowMeanCoreBlock12_kernel : lowMeanCoreBlock12.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock12, List.all_append, lowMean_fiberGroup0479_kernel, lowMean_fiberGroup0481_kernel, lowMean_fiberGroup0483_kernel, lowMean_fiberGroup0485_kernel, lowMean_fiberGroup0487_kernel, lowMean_fiberGroup0489_kernel, lowMean_fiberGroup0491_kernel, lowMean_fiberGroup0493_kernel, lowMean_fiberGroup0495_kernel, lowMean_fiberGroup0497_kernel, lowMean_fiberGroup0499_kernel, lowMean_fiberGroup0501_kernel, lowMean_fiberGroup0503_kernel, lowMean_fiberGroup0505_kernel, lowMean_fiberGroup0507_kernel, lowMean_fiberGroup0509_kernel, lowMean_fiberGroup0511_kernel, lowMean_fiberGroup0513_kernel, lowMean_fiberGroup0515_kernel, lowMean_fiberGroup0517_kernel, Bool.and_self]

theorem lowMeanCoreBlock12_length : lowMeanCoreBlock12.length = 39 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
