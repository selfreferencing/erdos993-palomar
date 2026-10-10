module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_09_09.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_09 :
    ActivityDomain (groupLo 9) ∧ ActivityDomain (groupHi 9) ∧
    (groupLo 9:ℝ)≤groupHi 9 ∧ (3/4:ℝ)≤groupLo 9 ∧
    (200:ℝ)<groupMargin 9 ∧
    (groupMargin 9:ℝ)/1000000≤highRate (q (groupLo 9))-groupBar 9 ∧
    (groupMargin 9:ℝ)/1000000≤highRate (q (groupHi 9))-groupBar 9 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_09
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_09
