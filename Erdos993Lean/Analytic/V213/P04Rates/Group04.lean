module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_04_04.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_04 :
    ActivityDomain (groupLo 4) ∧ ActivityDomain (groupHi 4) ∧
    (groupLo 4:ℝ)≤groupHi 4 ∧ (groupHi 4:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 4 ∧
    (groupMargin 4:ℝ)/1000000≤lowRate (q (groupLo 4))-groupBar 4 ∧
    (groupMargin 4:ℝ)/1000000≤lowRate (q (groupHi 4))-groupBar 4 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_04
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_04
