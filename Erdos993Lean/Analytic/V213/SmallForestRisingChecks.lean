module

public import Erdos993Lean.Analytic.V213.SmallForestFiniteFormula

/-! Current printed finite operands only. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestFinite
open Finset SmallForestPrinted

-- rising_margins.01; r12:eq114 / rising table
-- 3 & 1 & 13 & -- & --\\
theorem rising_3_first_facts : RisingFacts rising_3_first := by decide +kernel

-- rising_margins.02; r12:eq114 / rising table
-- 4 & 3 & 32 & 3 & 4\\
theorem rising_4_first_facts : RisingFacts rising_4_first := by decide +kernel

-- rising_margins.02; r12:eq114 / rising table
-- 4 & 3 & 32 & 3 & 4\\
theorem rising_4_second_facts : RisingFacts rising_4_second := by decide +kernel

-- rising_margins.03; r12:eq114 / rising table
-- 5 & 5 & 72 & 4 & 5\\
theorem rising_5_first_facts : RisingFacts rising_5_first := by decide +kernel

-- rising_margins.03; r12:eq114 / rising table
-- 5 & 5 & 72 & 4 & 5\\
theorem rising_5_second_facts : RisingFacts rising_5_second := by decide +kernel

-- rising_margins.04; r12:eq114 / rising table
-- 6 & 7 & 100 & 4 & 37\\
theorem rising_6_first_facts : RisingFacts rising_6_first := by decide +kernel

-- rising_margins.04; r12:eq114 / rising table
-- 6 & 7 & 100 & 4 & 37\\
theorem rising_6_second_facts : RisingFacts rising_6_second := by decide +kernel

-- rising_margins.05; r12:eq114 / rising table
-- 7 & 8 & 198 & 5 & 18\\
theorem rising_7_first_facts : RisingFacts rising_7_first := by decide +kernel

-- rising_margins.05; r12:eq114 / rising table
-- 7 & 8 & 198 & 5 & 18\\
theorem rising_7_second_facts : RisingFacts rising_7_second := by decide +kernel

-- rising_margins.06; r12:eq114 / rising table
-- 8 & 8 & 1348 & 5 & 183\\
theorem rising_8_first_facts : RisingFacts rising_8_first := by decide +kernel

-- rising_margins.06; r12:eq114 / rising table
-- 8 & 8 & 1348 & 5 & 183\\
theorem rising_8_second_facts : RisingFacts rising_8_second := by decide +kernel

-- rising_margins.07; r12:eq114 / rising table
-- 9 & 7 & 8941 & 5 & 902\\
theorem rising_9_first_facts : RisingFacts rising_9_first := by decide +kernel

-- rising_margins.07; r12:eq114 / rising table
-- 9 & 7 & 8941 & 5 & 902\\
theorem rising_9_second_facts : RisingFacts rising_9_second := by decide +kernel

-- rising_margins.08; r12:eq114 / rising table
-- 10 & 5 & 45802 & 5 & 3812\\
theorem rising_10_first_facts : RisingFacts rising_10_first := by decide +kernel

-- rising_margins.08; r12:eq114 / rising table
-- 10 & 5 & 45802 & 5 & 3812\\
theorem rising_10_second_facts : RisingFacts rising_10_second := by decide +kernel

-- rising_margins.09; r12:eq114 / rising table
-- 11 & 3 & 188707 & -- & --\\
theorem rising_11_first_facts : RisingFacts rising_11_first := by decide +kernel

theorem all_rising_facts : ∀ r ∈ risingInputs, RisingFacts r := by
  intro r hr
  simp only [risingInputs, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact rising_3_first_facts
  · exact rising_4_first_facts
  · exact rising_4_second_facts
  · exact rising_5_first_facts
  · exact rising_5_second_facts
  · exact rising_6_first_facts
  · exact rising_6_second_facts
  · exact rising_7_first_facts
  · exact rising_7_second_facts
  · exact rising_8_first_facts
  · exact rising_8_second_facts
  · exact rising_9_first_facts
  · exact rising_9_second_facts
  · exact rising_10_first_facts
  · exact rising_10_second_facts
  · exact rising_11_first_facts

end Erdos993Lean.Analytic.V213.SmallForestFinite

#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_3_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_3_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_4_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_4_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_4_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_4_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_5_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_5_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_5_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_5_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_6_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_6_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_6_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_6_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_7_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_7_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_7_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_7_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_8_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_8_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_8_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_8_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_9_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_9_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_9_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_9_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_10_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_10_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_10_second_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_10_second_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.rising_11_first_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.rising_11_first_facts
#check Erdos993Lean.Analytic.V213.SmallForestFinite.all_rising_facts
#print axioms Erdos993Lean.Analytic.V213.SmallForestFinite.all_rising_facts
