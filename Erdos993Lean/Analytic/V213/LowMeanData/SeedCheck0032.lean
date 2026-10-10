module

public import Erdos993Lean.Analytic.V213.LowMeanCoreAll
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0032
public import Erdos993Lean.Analytic.V213.LowMeanData.Seed0528
public import Erdos993Lean.Analytic.V213.LowMeanSeedGeometry
public import Erdos993Lean.Analytic.V213.LowMeanWidthData
public import Erdos993Lean.LowMeanFast.FastSeed

/-! Complete core-budget and stronger-target bindings, fibers 32--47. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

theorem lowMean_seedGroup0032_kernel : lowMeanSeedGroup0032.all
    (fun s => lowMeanDirectSeedCheck lowMeanWidthPairs (lowMeanCoreFiberAt s.record) s) = true := by
  exact Erdos993Lean.LowMeanFast.fastSeedGroup_sound _ (by decide +kernel)

end Erdos993Lean.Analytic.V213

#print axioms Erdos993Lean.Analytic.V213.lowMean_seedGroup0032_kernel
