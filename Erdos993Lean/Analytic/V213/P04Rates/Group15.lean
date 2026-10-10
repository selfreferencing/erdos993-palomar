module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_23_24.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_15 :
    ActivityDomain (groupLo 15) ∧ ActivityDomain (groupHi 15) ∧
    (groupLo 15:ℝ)≤groupHi 15 ∧ (3/4:ℝ)≤groupLo 15 ∧
    (200:ℝ)<groupMargin 15 ∧
    (groupMargin 15:ℝ)/1000000≤highRate (q (groupLo 15))-groupBar 15 ∧
    (groupMargin 15:ℝ)/1000000≤highRate (q (groupHi 15))-groupBar 15 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_15
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_15
