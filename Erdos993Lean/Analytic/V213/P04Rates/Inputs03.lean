module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input15; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_15 :
    inputLo 15=N44.Data.pieceLo.getD 15 0 ∧
    inputHi 15=N44.Data.pieceHi.getD 15 0 ∧
    inputRate 15=(N44.Data.rates44.getD 15 []).getD 0 0 ∧
    groupLo (groupOf 15)≤ inputLo 15 ∧ inputHi 15≤groupHi (groupOf 15) ∧
    inputRate 15≤groupBar (groupOf 15) ∧ groupOf 15<23 := by
  exact IntInput.original_input_fact 15 (by decide +kernel)

/-- Retained source input16; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_16 :
    inputLo 16=N44.Data.pieceLo.getD 16 0 ∧
    inputHi 16=N44.Data.pieceHi.getD 16 0 ∧
    inputRate 16=(N44.Data.rates44.getD 16 []).getD 0 0 ∧
    groupLo (groupOf 16)≤ inputLo 16 ∧ inputHi 16≤groupHi (groupOf 16) ∧
    inputRate 16≤groupBar (groupOf 16) ∧ groupOf 16<23 := by
  exact IntInput.original_input_fact 16 (by decide +kernel)

/-- Retained source input17; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_17 :
    inputLo 17=N44.Data.pieceLo.getD 17 0 ∧
    inputHi 17=N44.Data.pieceHi.getD 17 0 ∧
    inputRate 17=(N44.Data.rates44.getD 17 []).getD 0 0 ∧
    groupLo (groupOf 17)≤ inputLo 17 ∧ inputHi 17≤groupHi (groupOf 17) ∧
    inputRate 17≤groupBar (groupOf 17) ∧ groupOf 17<23 := by
  exact IntInput.original_input_fact 17 (by decide +kernel)

/-- Retained source input18; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_18 :
    inputLo 18=N44.Data.pieceLo.getD 18 0 ∧
    inputHi 18=N44.Data.pieceHi.getD 18 0 ∧
    inputRate 18=(N44.Data.rates44.getD 18 []).getD 0 0 ∧
    groupLo (groupOf 18)≤ inputLo 18 ∧ inputHi 18≤groupHi (groupOf 18) ∧
    inputRate 18≤groupBar (groupOf 18) ∧ groupOf 18<23 := by
  exact IntInput.original_input_fact 18 (by decide +kernel)

/-- Retained source input19; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_19 :
    inputLo 19=N44.Data.pieceLo.getD 19 0 ∧
    inputHi 19=N44.Data.pieceHi.getD 19 0 ∧
    inputRate 19=(N44.Data.rates44.getD 19 []).getD 0 0 ∧
    groupLo (groupOf 19)≤ inputLo 19 ∧ inputHi 19≤groupHi (groupOf 19) ∧
    inputRate 19≤groupBar (groupOf 19) ∧ groupOf 19<23 := by
  exact IntInput.original_input_fact 19 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_15
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_15
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_16
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_16
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_17
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_17
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_18
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_18
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_19
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_19
