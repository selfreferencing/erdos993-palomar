module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input5; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_05 :
    inputLo 5=N44.Data.pieceLo.getD 5 0 ∧
    inputHi 5=N44.Data.pieceHi.getD 5 0 ∧
    inputRate 5=(N44.Data.rates44.getD 5 []).getD 0 0 ∧
    groupLo (groupOf 5)≤ inputLo 5 ∧ inputHi 5≤groupHi (groupOf 5) ∧
    inputRate 5≤groupBar (groupOf 5) ∧ groupOf 5<23 := by
  exact IntInput.original_input_fact 5 (by decide +kernel)

/-- Retained source input6; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_06 :
    inputLo 6=N44.Data.pieceLo.getD 6 0 ∧
    inputHi 6=N44.Data.pieceHi.getD 6 0 ∧
    inputRate 6=(N44.Data.rates44.getD 6 []).getD 0 0 ∧
    groupLo (groupOf 6)≤ inputLo 6 ∧ inputHi 6≤groupHi (groupOf 6) ∧
    inputRate 6≤groupBar (groupOf 6) ∧ groupOf 6<23 := by
  exact IntInput.original_input_fact 6 (by decide +kernel)

/-- Retained source input7; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_07 :
    inputLo 7=N44.Data.pieceLo.getD 7 0 ∧
    inputHi 7=N44.Data.pieceHi.getD 7 0 ∧
    inputRate 7=(N44.Data.rates44.getD 7 []).getD 0 0 ∧
    groupLo (groupOf 7)≤ inputLo 7 ∧ inputHi 7≤groupHi (groupOf 7) ∧
    inputRate 7≤groupBar (groupOf 7) ∧ groupOf 7<23 := by
  exact IntInput.original_input_fact 7 (by decide +kernel)

/-- Retained source input8; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_08 :
    inputLo 8=N44.Data.pieceLo.getD 8 0 ∧
    inputHi 8=N44.Data.pieceHi.getD 8 0 ∧
    inputRate 8=(N44.Data.rates44.getD 8 []).getD 0 0 ∧
    groupLo (groupOf 8)≤ inputLo 8 ∧ inputHi 8≤groupHi (groupOf 8) ∧
    inputRate 8≤groupBar (groupOf 8) ∧ groupOf 8<23 := by
  exact IntInput.original_input_fact 8 (by decide +kernel)

/-- Retained source input9; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_09 :
    inputLo 9=N44.Data.pieceLo.getD 9 0 ∧
    inputHi 9=N44.Data.pieceHi.getD 9 0 ∧
    inputRate 9=(N44.Data.rates44.getD 9 []).getD 0 0 ∧
    groupLo (groupOf 9)≤ inputLo 9 ∧ inputHi 9≤groupHi (groupOf 9) ∧
    inputRate 9≤groupBar (groupOf 9) ∧ groupOf 9<23 := by
  exact IntInput.original_input_fact 9 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_05
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_05
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_06
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_06
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_07
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_07
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_08
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_08
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_09
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_09
