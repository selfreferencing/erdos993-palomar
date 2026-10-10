module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.09; r12:tab5
-- 9 & 13 & 7 & $1/2$ & $[6,10]$ & $(11,9,7)$ & $228$ & $234$ & $-199/30$\\
theorem family_9_endpoints : FamilyEndpointFacts family_9 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_9_margins : FamilyMargins family_9 := by decide +kernel

-- finite_differences.07; r12:eq119–120 / difference table
-- 9 & $(-29,-154,-132)$ & $(1669/105,2431/280,443/210,317/420)$\\
theorem family_9_differences : DifferenceFacts family_9 differences_9 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_9_differences
