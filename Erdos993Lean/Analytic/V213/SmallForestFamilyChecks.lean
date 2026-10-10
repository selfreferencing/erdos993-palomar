module

public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks01
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks02
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks03
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks04
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks05
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks06
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks07
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks08
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks09
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks10
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks11
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks12
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks13
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks14
public import Erdos993Lean.Analytic.V213.SmallForestFamilyChecks15

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

theorem all_family_endpoints : ∀ r ∈ familyInputs, FamilyEndpointFacts r := by
  intro r hr
  simp only [familyInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family_1_endpoints
  · exact family_2_endpoints
  · exact family_3_endpoints
  · exact family_4_endpoints
  · exact family_5_endpoints
  · exact family_6_endpoints
  · exact family_7_endpoints
  · exact family_8_endpoints
  · exact family_9_endpoints
  · exact family_10_endpoints
  · exact family_11_endpoints
  · exact family_12_endpoints
  · exact family_13_endpoints
  · exact family_14_endpoints
  · exact family_15_endpoints

theorem all_family_margins : ∀ r ∈ familyInputs, FamilyMargins r := by
  intro r hr
  simp only [familyInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact family_1_margins
  · exact family_2_margins
  · exact family_3_margins
  · exact family_4_margins
  · exact family_5_margins
  · exact family_6_margins
  · exact family_7_margins
  · exact family_8_margins
  · exact family_9_margins
  · exact family_10_margins
  · exact family_11_margins
  · exact family_12_margins
  · exact family_13_margins
  · exact family_14_margins
  · exact family_15_margins

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.all_family_endpoints
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.all_family_endpoints
#check Erdos993Lean.Analytic.V213.SmallForestFinite.all_family_margins
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.all_family_margins
