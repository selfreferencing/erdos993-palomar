module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input10; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_10 :
    inputLo 10=N44.Data.pieceLo.getD 10 0 ∧
    inputHi 10=N44.Data.pieceHi.getD 10 0 ∧
    inputRate 10=(N44.Data.rates44.getD 10 []).getD 0 0 ∧
    groupLo (groupOf 10)≤ inputLo 10 ∧ inputHi 10≤groupHi (groupOf 10) ∧
    inputRate 10≤groupBar (groupOf 10) ∧ groupOf 10<23 := by
  exact IntInput.original_input_fact 10 (by decide +kernel)

/-- Retained source input11; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_11 :
    inputLo 11=N44.Data.pieceLo.getD 11 0 ∧
    inputHi 11=N44.Data.pieceHi.getD 11 0 ∧
    inputRate 11=(N44.Data.rates44.getD 11 []).getD 0 0 ∧
    groupLo (groupOf 11)≤ inputLo 11 ∧ inputHi 11≤groupHi (groupOf 11) ∧
    inputRate 11≤groupBar (groupOf 11) ∧ groupOf 11<23 := by
  exact IntInput.original_input_fact 11 (by decide +kernel)

/-- Retained source input12; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_12 :
    inputLo 12=N44.Data.pieceLo.getD 12 0 ∧
    inputHi 12=N44.Data.pieceHi.getD 12 0 ∧
    inputRate 12=(N44.Data.rates44.getD 12 []).getD 0 0 ∧
    groupLo (groupOf 12)≤ inputLo 12 ∧ inputHi 12≤groupHi (groupOf 12) ∧
    inputRate 12≤groupBar (groupOf 12) ∧ groupOf 12<23 := by
  exact IntInput.original_input_fact 12 (by decide +kernel)

/-- Retained source input13; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_13 :
    inputLo 13=N44.Data.pieceLo.getD 13 0 ∧
    inputHi 13=N44.Data.pieceHi.getD 13 0 ∧
    inputRate 13=(N44.Data.rates44.getD 13 []).getD 0 0 ∧
    groupLo (groupOf 13)≤ inputLo 13 ∧ inputHi 13≤groupHi (groupOf 13) ∧
    inputRate 13≤groupBar (groupOf 13) ∧ groupOf 13<23 := by
  exact IntInput.original_input_fact 13 (by decide +kernel)

/-- Retained source input14; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_14 :
    inputLo 14=N44.Data.pieceLo.getD 14 0 ∧
    inputHi 14=N44.Data.pieceHi.getD 14 0 ∧
    inputRate 14=(N44.Data.rates44.getD 14 []).getD 0 0 ∧
    groupLo (groupOf 14)≤ inputLo 14 ∧ inputHi 14≤groupHi (groupOf 14) ∧
    inputRate 14≤groupBar (groupOf 14) ∧ groupOf 14<23 := by
  exact IntInput.original_input_fact 14 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_10
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_10
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_11
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_11
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_12
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_12
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_13
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_13
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_14
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_14
