module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_25_25.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_16 :
    ActivityDomain (groupLo 16) ∧ ActivityDomain (groupHi 16) ∧
    (groupLo 16:ℝ)≤groupHi 16 ∧ (3/4:ℝ)≤groupLo 16 ∧
    (200:ℝ)<groupMargin 16 ∧
    (groupMargin 16:ℝ)/1000000≤highRate (q (groupLo 16))-groupBar 16 ∧
    (groupMargin 16:ℝ)/1000000≤highRate (q (groupHi 16))-groupBar 16 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_16
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_16
