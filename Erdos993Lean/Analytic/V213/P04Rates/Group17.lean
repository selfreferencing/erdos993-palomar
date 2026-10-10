module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_26_27.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_17 :
    ActivityDomain (groupLo 17) ∧ ActivityDomain (groupHi 17) ∧
    (groupLo 17:ℝ)≤groupHi 17 ∧ (3/4:ℝ)≤groupLo 17 ∧
    (200:ℝ)<groupMargin 17 ∧
    (groupMargin 17:ℝ)/1000000≤highRate (q (groupLo 17))-groupBar 17 ∧
    (groupMargin 17:ℝ)/1000000≤highRate (q (groupHi 17))-groupBar 17 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_17
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_17
