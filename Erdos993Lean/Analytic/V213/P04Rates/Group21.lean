module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_50_50.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_21 :
    ActivityDomain (groupLo 21) ∧ ActivityDomain (groupHi 21) ∧
    (groupLo 21:ℝ)≤groupHi 21 ∧ (3/4:ℝ)≤groupLo 21 ∧
    (200:ℝ)<groupMargin 21 ∧
    (groupMargin 21:ℝ)/1000000≤highRate (q (groupLo 21))-groupBar 21 ∧
    (groupMargin 21:ℝ)/1000000≤highRate (q (groupHi 21))-groupBar 21 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_21
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_21
