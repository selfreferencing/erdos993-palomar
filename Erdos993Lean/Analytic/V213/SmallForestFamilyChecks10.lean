module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.10; r12:tab5
-- 10 & 14 & 7 & $1/2$ & $[6,6]$ & $(11,8,6)$ & $721$ & $721$ & $62/15$\\
theorem family_10_endpoints : FamilyEndpointFacts family_10 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_10_margins : FamilyMargins family_10 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_10_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_10_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_10_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_10_margins
