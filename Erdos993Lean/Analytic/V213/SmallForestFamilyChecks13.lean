module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.13; r12:tab5
-- 13 & 16 & 8 & $1/2$ & $[7,7]$ & $(13,10,8)$ & $4593/2$ & $4593/2$ & $881/21$\\
theorem family_13_endpoints : FamilyEndpointFacts family_13 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_13_margins : FamilyMargins family_13 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_13_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_13_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_13_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_13_margins
