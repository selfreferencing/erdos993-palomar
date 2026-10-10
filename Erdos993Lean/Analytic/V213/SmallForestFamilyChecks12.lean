module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.12; r12:tab5
-- 12 & 15 & 8 & $1/2$ & $[6,9]$ & $(13,10,7)$ & $1551/2$ & $1783/2$ & $1057/10$\\
theorem family_12_endpoints : FamilyEndpointFacts family_12 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_12_margins : FamilyMargins family_12 := by decide +kernel

-- finite_differences.09; r12:eq119–120 / difference table
-- 12 & $(-241,-863/2)$ & $(2864/105,8983/840,14561/2520)$\\
theorem family_12_differences : DifferenceFacts family_12 differences_12 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_12_differences
