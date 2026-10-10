module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.07; r12:tab5
-- 7 & 12 & 7 & $1/2$ & $[9,11]$ & $(10,9,7,4)$ & $394$ & $444$ & $445/24$\\
theorem family_7_endpoints : FamilyEndpointFacts family_7 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_7_margins : FamilyMargins family_7 := by decide +kernel

-- finite_differences.06; r12:eq119–120 / difference table
-- 7 & $(-284)$ & $(3611/120,551/40)$\\
theorem family_7_differences : DifferenceFacts family_7 differences_7 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_7_differences
