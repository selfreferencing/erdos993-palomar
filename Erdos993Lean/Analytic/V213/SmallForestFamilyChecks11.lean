module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.11; r12:tab5
-- 11 & 14 & 8 & $1/2$ & $[9,10]$ & $(12,10,8,5)$ & $731$ & $662$ & $6415/72$\\
theorem family_11_endpoints : FamilyEndpointFacts family_11 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_11_margins : FamilyMargins family_11 := by decide +kernel

-- finite_differences.08; r12:eq119–120 / difference table
-- 11 & -- & $(20573/360)$\\
theorem family_11_differences : DifferenceFacts family_11 differences_11 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_margins
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_differences
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_11_differences
