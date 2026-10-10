module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.15; r12:tab5
-- 15 & 18 & 9 & $1/2$ & $[6,6]$ & $(15,11)$ & $6535$ & $6535$ & $6427/15$\\
theorem family_15_endpoints : FamilyEndpointFacts family_15 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_15_margins : FamilyMargins family_15 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_15_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_15_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_15_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_15_margins
