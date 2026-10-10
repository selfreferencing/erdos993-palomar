module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.05; r12:tab5
-- 5 & 11 & 6 & $1/2$ & $[6,9]$ & $(9,7,4)$ & $155$ & $188$ & $32/5$\\
theorem family_5_endpoints : FamilyEndpointFacts family_5 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_5_margins : FamilyMargins family_5 := by decide +kernel

-- finite_differences.04; r12:eq119–120 / difference table
-- 5 & $(-37,-66)$ & $(226/35,361/140,26/35)$\\
theorem family_5_differences : DifferenceFacts family_5 differences_5 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_5_differences
