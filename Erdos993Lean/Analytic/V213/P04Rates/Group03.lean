module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_03_03.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_03 :
    ActivityDomain (groupLo 3) ∧ ActivityDomain (groupHi 3) ∧
    (groupLo 3:ℝ)≤groupHi 3 ∧ (groupHi 3:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 3 ∧
    (groupMargin 3:ℝ)/1000000≤lowRate (q (groupLo 3))-groupBar 3 ∧
    (groupMargin 3:ℝ)/1000000≤lowRate (q (groupHi 3))-groupBar 3 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_03
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_03
