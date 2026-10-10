module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.03; r12:tab5
-- 3 & 10 & 5 & $1/2$ & $[5,6]$ & $(8,4)$ & $161/2$ & $83$ & $143/20$\\
theorem family_3_endpoints : FamilyEndpointFacts family_3 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_3_margins : FamilyMargins family_3 := by decide +kernel

-- finite_differences.02; r12:eq119–120 / difference table
-- 3 & -- & $(53/20)$\\
theorem family_3_differences : DifferenceFacts family_3 differences_3 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_3_differences
