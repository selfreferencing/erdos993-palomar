module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_14_16.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_11 :
    ActivityDomain (groupLo 11) ∧ ActivityDomain (groupHi 11) ∧
    (groupLo 11:ℝ)≤groupHi 11 ∧ (3/4:ℝ)≤groupLo 11 ∧
    (200:ℝ)<groupMargin 11 ∧
    (groupMargin 11:ℝ)/1000000≤highRate (q (groupLo 11))-groupBar 11 ∧
    (groupMargin 11:ℝ)/1000000≤highRate (q (groupHi 11))-groupBar 11 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_11
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_11
