module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- family_endpoints.08; r12:tab5
-- 8 & 12 & 7 & $2/3$ & $[12,12]$ & $(11,9,8,6,3)$ & $7051/3$ & $7051/3$ & $-229/2$\\
theorem family_8_endpoints : FamilyEndpointFacts family_8 := by decide +kernel

-- All integer c in this printed interval; no new external certificate list.
theorem family_8_margins : FamilyMargins family_8 := by decide +kernel

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_8_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_8_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.family_8_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.family_8_margins
