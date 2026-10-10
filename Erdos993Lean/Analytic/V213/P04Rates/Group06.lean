module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_06_06.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_06 :
    ActivityDomain (groupLo 6) ∧ ActivityDomain (groupHi 6) ∧
    (groupLo 6:ℝ)≤groupHi 6 ∧ (groupHi 6:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 6 ∧
    (groupMargin 6:ℝ)/1000000≤lowRate (q (groupLo 6))-groupBar 6 ∧
    (groupMargin 6:ℝ)/1000000≤lowRate (q (groupHi 6))-groupBar 6 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_06
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_06
