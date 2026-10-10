module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input0; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_00 :
    inputLo 0=N44.Data.pieceLo.getD 0 0 ∧
    inputHi 0=N44.Data.pieceHi.getD 0 0 ∧
    inputRate 0=(N44.Data.rates44.getD 0 []).getD 0 0 ∧
    groupLo (groupOf 0)≤ inputLo 0 ∧ inputHi 0≤groupHi (groupOf 0) ∧
    inputRate 0≤groupBar (groupOf 0) ∧ groupOf 0<23 := by
  exact IntInput.original_input_fact 0 (by decide +kernel)

/-- Retained source input1; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_01 :
    inputLo 1=N44.Data.pieceLo.getD 1 0 ∧
    inputHi 1=N44.Data.pieceHi.getD 1 0 ∧
    inputRate 1=(N44.Data.rates44.getD 1 []).getD 0 0 ∧
    groupLo (groupOf 1)≤ inputLo 1 ∧ inputHi 1≤groupHi (groupOf 1) ∧
    inputRate 1≤groupBar (groupOf 1) ∧ groupOf 1<23 := by
  exact IntInput.original_input_fact 1 (by decide +kernel)

/-- Retained source input2; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_02 :
    inputLo 2=N44.Data.pieceLo.getD 2 0 ∧
    inputHi 2=N44.Data.pieceHi.getD 2 0 ∧
    inputRate 2=(N44.Data.rates44.getD 2 []).getD 0 0 ∧
    groupLo (groupOf 2)≤ inputLo 2 ∧ inputHi 2≤groupHi (groupOf 2) ∧
    inputRate 2≤groupBar (groupOf 2) ∧ groupOf 2<23 := by
  exact IntInput.original_input_fact 2 (by decide +kernel)

/-- Retained source input3; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_03 :
    inputLo 3=N44.Data.pieceLo.getD 3 0 ∧
    inputHi 3=N44.Data.pieceHi.getD 3 0 ∧
    inputRate 3=(N44.Data.rates44.getD 3 []).getD 0 0 ∧
    groupLo (groupOf 3)≤ inputLo 3 ∧ inputHi 3≤groupHi (groupOf 3) ∧
    inputRate 3≤groupBar (groupOf 3) ∧ groupOf 3<23 := by
  exact IntInput.original_input_fact 3 (by decide +kernel)

/-- Retained source input4; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_04 :
    inputLo 4=N44.Data.pieceLo.getD 4 0 ∧
    inputHi 4=N44.Data.pieceHi.getD 4 0 ∧
    inputRate 4=(N44.Data.rates44.getD 4 []).getD 0 0 ∧
    groupLo (groupOf 4)≤ inputLo 4 ∧ inputHi 4≤groupHi (groupOf 4) ∧
    inputRate 4≤groupBar (groupOf 4) ∧ groupOf 4<23 := by
  exact IntInput.original_input_fact 4 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_00
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_00
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_01
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_01
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_02
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_02
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_03
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_03
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_04
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_04
