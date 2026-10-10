module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_18_20.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_13 :
    ActivityDomain (groupLo 13) ∧ ActivityDomain (groupHi 13) ∧
    (groupLo 13:ℝ)≤groupHi 13 ∧ (3/4:ℝ)≤groupLo 13 ∧
    (200:ℝ)<groupMargin 13 ∧
    (groupMargin 13:ℝ)/1000000≤highRate (q (groupLo 13))-groupBar 13 ∧
    (groupMargin 13:ℝ)/1000000≤highRate (q (groupHi 13))-groupBar 13 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_13
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_13
