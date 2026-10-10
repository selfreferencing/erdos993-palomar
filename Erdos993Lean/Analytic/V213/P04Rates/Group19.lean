module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_37_43.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_19 :
    ActivityDomain (groupLo 19) ∧ ActivityDomain (groupHi 19) ∧
    (groupLo 19:ℝ)≤groupHi 19 ∧ (3/4:ℝ)≤groupLo 19 ∧
    (200:ℝ)<groupMargin 19 ∧
    (groupMargin 19:ℝ)/1000000≤highRate (q (groupLo 19))-groupBar 19 ∧
    (groupMargin 19:ℝ)/1000000≤highRate (q (groupHi 19))-groupBar 19 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,highRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_19
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_19
