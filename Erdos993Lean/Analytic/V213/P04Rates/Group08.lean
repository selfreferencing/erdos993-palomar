module

public import Erdos993Lean.Analytic.V213.P04Rates.Data

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-! P04_RATE_GROUP_08_08.
Use the low extension at the right endpoint3/4 when present. -/

theorem group_endpoints_08 :
    ActivityDomain (groupLo 8) ∧ ActivityDomain (groupHi 8) ∧
    (groupLo 8:ℝ)≤groupHi 8 ∧ (groupHi 8:ℝ)≤3/4 ∧
    (200:ℝ)<groupMargin 8 ∧
    (groupMargin 8:ℝ)/1000000≤lowRate (q (groupLo 8))-groupBar 8 ∧
    (groupMargin 8:ℝ)/1000000≤lowRate (q (groupHi 8))-groupBar 8 := by
  norm_num [ActivityDomain,groupLo,groupHi,groupBar,groupMargin,q,lowRate,rateR]

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_08
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.group_endpoints_08
