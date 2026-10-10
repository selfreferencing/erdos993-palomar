module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_01_01.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_01 :
    ActivityDomain (groupLo 1) ∧ ActivityDomain (groupHi 1) ∧
    (groupLo 1:ℝ)≤groupHi 1 ∧ (groupHi 1:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 1 ∧
    (groupMargin 1:ℝ)/1000000≤lowRate (q (groupLo 1))-groupBar 1 ∧
    (groupMargin 1:ℝ)/1000000≤lowRate (q (groupHi 1))-groupBar 1 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_01
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_01
