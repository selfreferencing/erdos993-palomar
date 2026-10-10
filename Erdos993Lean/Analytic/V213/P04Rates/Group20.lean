module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_44_49.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_20 :
    ActivityDomain (groupLo 20) ∧ ActivityDomain (groupHi 20) ∧
    (groupLo 20:ℝ)≤groupHi 20 ∧ (3/4:ℝ)≤groupLo 20 ∧
    (200:ℝ)<groupMargin 20 ∧
    (groupMargin 20:ℝ)/1000000≤highRate (q (groupLo 20))-groupBar 20 ∧
    (groupMargin 20:ℝ)/1000000≤highRate (q (groupHi 20))-groupBar 20 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_20
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_20
