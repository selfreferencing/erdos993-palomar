module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_17_17.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_12 :
    ActivityDomain (groupLo 12) ∧ ActivityDomain (groupHi 12) ∧
    (groupLo 12:ℝ)≤groupHi 12 ∧ (3/4:ℝ)≤groupLo 12 ∧
    (200:ℝ)<groupMargin 12 ∧
    (groupMargin 12:ℝ)/1000000≤highRate (q (groupLo 12))-groupBar 12 ∧
    (groupMargin 12:ℝ)/1000000≤highRate (q (groupHi 12))-groupBar 12 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_12
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_12
