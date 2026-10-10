module

public import Erdos993Lean.Analytic.V213.LowMeanCoreChecker
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0159
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0161
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0163
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0165
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0167
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0169
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0171
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0173
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0175
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0177
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0179
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0181
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0183
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0185
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0187
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0189
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0191
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0193
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0195
public import Erdos993Lean.Analytic.V213.LowMeanData.Fiber0197
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0159
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0161
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0163
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0165
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0167
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0169
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0171
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0173
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0175
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0177
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0179
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0181
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0183
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0185
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0187
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0189
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0191
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0193
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0195
public import Erdos993Lean.Analytic.V213.LowMeanData.FiberCheck0197

/-! Complete frozen core block 4, fibers 159--198. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

noncomputable def lowMeanCoreBlock04 : List LowMeanFiberInput :=
  lowMeanFiberGroup0159 ++ lowMeanFiberGroup0161 ++ lowMeanFiberGroup0163 ++ lowMeanFiberGroup0165 ++ lowMeanFiberGroup0167 ++ lowMeanFiberGroup0169 ++ lowMeanFiberGroup0171 ++ lowMeanFiberGroup0173 ++ lowMeanFiberGroup0175 ++ lowMeanFiberGroup0177 ++ lowMeanFiberGroup0179 ++ lowMeanFiberGroup0181 ++ lowMeanFiberGroup0183 ++ lowMeanFiberGroup0185 ++ lowMeanFiberGroup0187 ++ lowMeanFiberGroup0189 ++ lowMeanFiberGroup0191 ++ lowMeanFiberGroup0193 ++ lowMeanFiberGroup0195 ++ lowMeanFiberGroup0197

theorem lowMeanCoreBlock04_kernel : lowMeanCoreBlock04.all lowMeanFiberCheck = true := by
  simp only [lowMeanCoreBlock04, List.all_append, lowMean_fiberGroup0159_kernel, lowMean_fiberGroup0161_kernel, lowMean_fiberGroup0163_kernel, lowMean_fiberGroup0165_kernel, lowMean_fiberGroup0167_kernel, lowMean_fiberGroup0169_kernel, lowMean_fiberGroup0171_kernel, lowMean_fiberGroup0173_kernel, lowMean_fiberGroup0175_kernel, lowMean_fiberGroup0177_kernel, lowMean_fiberGroup0179_kernel, lowMean_fiberGroup0181_kernel, lowMean_fiberGroup0183_kernel, lowMean_fiberGroup0185_kernel, lowMean_fiberGroup0187_kernel, lowMean_fiberGroup0189_kernel, lowMean_fiberGroup0191_kernel, lowMean_fiberGroup0193_kernel, lowMean_fiberGroup0195_kernel, lowMean_fiberGroup0197_kernel, Bool.and_self]

theorem lowMeanCoreBlock04_length : lowMeanCoreBlock04.length = 40 := by
  decide +kernel

end Erdos993Lean.Analytic.V213
