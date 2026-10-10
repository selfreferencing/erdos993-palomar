module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.04; r12:tab5
-- 4 & 10 & 6 & $1/2$ & $[9,10]$ & $(8,7,5,2)$ & $272$ & $329$ & $79/12$\\
theorem family_4_endpoints : FamilyEndpointFacts family_4 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_4_margins : FamilyMargins family_4 := by decide +kernel

-- finite_differences.03; r12:eq119–120 / difference table
-- 4 & -- & $(793/60)$\\
theorem family_4_differences : DifferenceFacts family_4 differences_4 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_4_differences
