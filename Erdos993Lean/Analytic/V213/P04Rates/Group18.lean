module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_28_36.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_18 :
    ActivityDomain (groupLo 18) ∧ ActivityDomain (groupHi 18) ∧
    (groupLo 18:ℝ)≤groupHi 18 ∧ (3/4:ℝ)≤groupLo 18 ∧
    (200:ℝ)<groupMargin 18 ∧
    (groupMargin 18:ℝ)/1000000≤highRate (q (groupLo 18))-groupBar 18 ∧
    (groupMargin 18:ℝ)/1000000≤highRate (q (groupHi 18))-groupBar 18 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_18
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_18
