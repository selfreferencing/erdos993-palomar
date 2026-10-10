module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.06; r12:tab5
-- 6 & 12 & 6 & $1/2$ & $[5,8]$ & $(10,7)$ & $207$ & $79$ & $169/10$\\
theorem family_6_endpoints : FamilyEndpointFacts family_6 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_6_margins : FamilyMargins family_6 := by decide +kernel

-- finite_differences.05; r12:eq119–120 / difference table
-- 6 & $(-71,-83)$ & $(17/2,481/210,61/70)$\\
theorem family_6_differences : DifferenceFacts family_6 differences_6 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_6_differences
