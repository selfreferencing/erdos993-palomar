module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.14; r12:tab5
-- 14 & 17 & 9 & $1/2$ & $[6,7]$ & $(14,10)$ & $2973$ & $3238$ & $6977/30$\\
theorem family_14_endpoints : FamilyEndpointFacts family_14 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_14_margins : FamilyMargins family_14 := by decide +kernel

-- finite_differences.10; r12:eq119–120 / difference table
-- 14 & -- & $(2158/105)$\\
theorem family_14_differences : DifferenceFacts family_14 differences_14 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_14_differences
