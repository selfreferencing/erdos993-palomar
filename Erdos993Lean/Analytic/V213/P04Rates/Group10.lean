module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_10_13.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_10 :
    ActivityDomain (groupLo 10) ∧ ActivityDomain (groupHi 10) ∧
    (groupLo 10:ℝ)≤groupHi 10 ∧ (3/4:ℝ)≤groupLo 10 ∧
    (200:ℝ)<groupMargin 10 ∧
    (groupMargin 10:ℝ)/1000000≤highRate (q (groupLo 10))-groupBar 10 ∧
    (groupMargin 10:ℝ)/1000000≤highRate (q (groupHi 10))-groupBar 10 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_10
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_10
