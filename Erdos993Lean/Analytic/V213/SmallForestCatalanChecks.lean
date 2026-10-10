module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- affine_catalan_named.01; r12:eq109 / eight affine Catalan cases
-- 15 & 7 & 9 & 3 & 3 & 5540 & 449/6\\
theorem catalan_named_1_facts : CatalanFacts catalan_named_1 := by decide +kernel

-- affine_catalan_named.02; r12:eq109 / eight affine Catalan cases
-- 13 & 7 & 11 & 3 & 5 & 1146 & 732/5\\
theorem catalan_named_2_facts : CatalanFacts catalan_named_2 := by decide +kernel

-- affine_catalan_named.03; r12:eq109 / eight affine Catalan cases
-- 16 & 8 & 6 & 0 & 1 & 36 & 2978/15\\
theorem catalan_named_3_facts : CatalanFacts catalan_named_3 := by decide +kernel

-- affine_catalan_named.04; r12:eq109 / eight affine Catalan cases
-- 16 & 8 & 8 & 1 & 4 & 87 & 1115/7\\
theorem catalan_named_4_facts : CatalanFacts catalan_named_4 := by decide +kernel

-- Exactly the four printed integer Newton points.
theorem a14_facts_0 : catalanAQ 14 (7+0) 7 1 4 = a14Constant 0 ∧ catalanBQ 14 (7+0) 7 1 4 = a14Slope 0 ∧ 232 ≤ a14Constant 0 ∧ 18 < a14Slope 0 := by decide +kernel

-- Exactly the four printed integer Newton points.
theorem a14_facts_1 : catalanAQ 14 (7+1) 7 1 4 = a14Constant 1 ∧ catalanBQ 14 (7+1) 7 1 4 = a14Slope 1 ∧ 232 ≤ a14Constant 1 ∧ 18 < a14Slope 1 := by decide +kernel

-- Exactly the four printed integer Newton points.
theorem a14_facts_2 : catalanAQ 14 (7+2) 7 1 4 = a14Constant 2 ∧ catalanBQ 14 (7+2) 7 1 4 = a14Slope 2 ∧ 232 ≤ a14Constant 2 ∧ 18 < a14Slope 2 := by decide +kernel

-- Exactly the four printed integer Newton points.
theorem a14_facts_3 : catalanAQ 14 (7+3) 7 1 4 = a14Constant 3 ∧ catalanBQ 14 (7+3) 7 1 4 = a14Slope 3 ∧ 232 ≤ a14Constant 3 ∧ 18 < a14Slope 3 := by decide +kernel

theorem all_named_catalan_facts : ∀ r ∈ namedCatalanInputs, CatalanFacts r := by
  intro r hr
  simp only [namedCatalanInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact catalan_named_1_facts
  · exact catalan_named_2_facts
  · exact catalan_named_3_facts
  · exact catalan_named_4_facts

theorem all_a14_facts : ∀ x ∈ a14Indices, catalanAQ 14 (7+x) 7 1 4 = a14Constant x ∧ catalanBQ 14 (7+x) 7 1 4 = a14Slope x ∧ 232 ≤ a14Constant x ∧ 18 < a14Slope x := by
  intro r hr
  simp only [a14Indices, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact a14_facts_0
  · exact a14_facts_1
  · exact a14_facts_2
  · exact a14_facts_3

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_1_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_1_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_2_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_2_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_3_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_3_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_4_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.catalan_named_4_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_0
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_0
#check Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_1
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_1
#check Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_2
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_2
#check Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_3
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.a14_facts_3
#check Erdos993Lean.Analytic.V213.SmallForestFinite.all_named_catalan_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.all_named_catalan_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.all_a14_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.all_a14_facts
