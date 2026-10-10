module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.02; r12:tab5
-- 2 & 9 & 5 & $1/2$ & $[6,7]$ & $(7,5,2)$ & $153/2$ & $201/2$ & $73/30$\\
theorem family_2_endpoints : FamilyEndpointFacts family_2 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_2_margins : FamilyMargins family_2 := by decide +kernel

-- finite_differences.01; r12:eq119–120 / difference table
-- 2 & -- & $(46/15)$\\
theorem family_2_differences : DifferenceFacts family_2 differences_2 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_2_differences
