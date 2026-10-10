module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_02_02.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_02 :
    ActivityDomain (groupLo 2) ∧ ActivityDomain (groupHi 2) ∧
    (groupLo 2:ℝ)≤groupHi 2 ∧ (groupHi 2:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 2 ∧
    (groupMargin 2:ℝ)/1000000≤lowRate (q (groupLo 2))-groupBar 2 ∧
    (groupMargin 2:ℝ)/1000000≤lowRate (q (groupHi 2))-groupBar 2 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_02
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_02
