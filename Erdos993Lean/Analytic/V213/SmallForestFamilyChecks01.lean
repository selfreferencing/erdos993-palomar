module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.01; r12:tab5
-- 1 & 8 & 4 & $1/2$ & $[4,4]$ & $(5,2)$ & $26$ & $26$ & $3/2$\\
theorem family_1_endpoints : FamilyEndpointFacts family_1 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_1_margins : FamilyMargins family_1 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_1_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_1_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_1_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_1_margins
