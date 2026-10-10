module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_05_05.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_05 :
    ActivityDomain (groupLo 5) ∧ ActivityDomain (groupHi 5) ∧
    (groupLo 5:ℝ)≤groupHi 5 ∧ (groupHi 5:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 5 ∧
    (groupMargin 5:ℝ)/1000000≤lowRate (q (groupLo 5))-groupBar 5 ∧
    (groupMargin 5:ℝ)/1000000≤lowRate (q (groupHi 5))-groupBar 5 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_05
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_05
