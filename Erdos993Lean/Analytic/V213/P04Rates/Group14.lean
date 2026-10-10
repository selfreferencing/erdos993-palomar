module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_21_22.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_14 :
    ActivityDomain (groupLo 14) ∧ ActivityDomain (groupHi 14) ∧
    (groupLo 14:ℝ)≤groupHi 14 ∧ (3/4:ℝ)≤groupLo 14 ∧
    (200:ℝ)<groupMargin 14 ∧
    (groupMargin 14:ℝ)/1000000≤highRate (q (groupLo 14))-groupBar 14 ∧
    (groupMargin 14:ℝ)/1000000≤highRate (q (groupHi 14))-groupBar 14 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_14
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_14
