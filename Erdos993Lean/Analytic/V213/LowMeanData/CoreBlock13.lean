module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0518Part0001
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0519Part0002
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0521
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0523
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0525
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0527
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0529
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0531
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0533
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0535
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0537
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0539
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0541
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0543
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0545
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0547
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0549
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0551
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0553
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0555
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0518
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0519
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0521
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0523
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0525
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0527
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0529
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0531
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0533
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0535
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0537
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0539
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0541
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0543
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0545
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0547
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0549
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0551
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0553
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0555

/-! Complete frozen core block 13, fibers 518--556. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock13 : List LowMeanFiberInput :=
  lowMeanFiberGroup0518 ++ lowMeanFiberGroup0519 ++ lowMeanFiberGroup0521 ++ lowMeanFiberGroup0523 ++ lowMeanFiberGroup0525 ++ lowMeanFiberGroup0527 ++ lowMeanFiberGroup0529 ++ lowMeanFiberGroup0531 ++ lowMeanFiberGroup0533 ++ lowMeanFiberGroup0535 ++ lowMeanFiberGroup0537 ++ lowMeanFiberGroup0539 ++ lowMeanFiberGroup0541 ++ lowMeanFiberGroup0543 ++ lowMeanFiberGroup0545 ++ lowMeanFiberGroup0547 ++ lowMeanFiberGroup0549 ++ lowMeanFiberGroup0551 ++ lowMeanFiberGroup0553 ++ lowMeanFiberGroup0555

theorem lowMeanCoreBlock13_kernel : lowMeanCoreBlock13.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock13, List.all_append, lowMean_fiberGroup0518_kernel, lowMean_fiberGroup0519_kernel, lowMean_fiberGroup0521_kernel, lowMean_fiberGroup0523_kernel, lowMean_fiberGroup0525_kernel, lowMean_fiberGroup0527_kernel, lowMean_fiberGroup0529_kernel, lowMean_fiberGroup0531_kernel, lowMean_fiberGroup0533_kernel, lowMean_fiberGroup0535_kernel, lowMean_fiberGroup0537_kernel, lowMean_fiberGroup0539_kernel, lowMean_fiberGroup0541_kernel, lowMean_fiberGroup0543_kernel, lowMean_fiberGroup0545_kernel, lowMean_fiberGroup0547_kernel, lowMean_fiberGroup0549_kernel, lowMean_fiberGroup0551_kernel, lowMean_fiberGroup0553_kernel, lowMean_fiberGroup0555_kernel, Bool.and_self]

theorem lowMeanCoreBlock13_length : lowMeanCoreBlock13.length = 39 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
