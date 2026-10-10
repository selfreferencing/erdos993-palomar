module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_51_54.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_22 :
    ActivityDomain (groupLo 22) ∧ ActivityDomain (groupHi 22) ∧
    (groupLo 22:ℝ)≤groupHi 22 ∧ (3/4:ℝ)≤groupLo 22 ∧
    (200:ℝ)<groupMargin 22 ∧
    (groupMargin 22:ℝ)/1000000≤highRate (q (groupLo 22))-groupBar 22 ∧
    (groupMargin 22:ℝ)/1000000≤highRate (q (groupHi 22))-groupBar 22 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_22
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_22
