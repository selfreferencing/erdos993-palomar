module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_07_07.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_07 :
    ActivityDomain (groupLo 7) ∧ ActivityDomain (groupHi 7) ∧
    (groupLo 7:ℝ)≤groupHi 7 ∧ (groupHi 7:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 7 ∧
    (groupMargin 7:ℝ)/1000000≤lowRate (q (groupLo 7))-groupBar 7 ∧
    (groupMargin 7:ℝ)/1000000≤lowRate (q (groupHi 7))-groupBar 7 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_07
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_07
