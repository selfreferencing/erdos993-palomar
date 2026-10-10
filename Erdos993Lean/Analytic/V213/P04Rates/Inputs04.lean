module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input20; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_20 :
    inputLo 20=N44.Data.pieceLo.getD 20 0 ∧
    inputHi 20=N44.Data.pieceHi.getD 20 0 ∧
    inputRate 20=(N44.Data.rates44.getD 20 []).getD 0 0 ∧
    groupLo (groupOf 20)≤ inputLo 20 ∧ inputHi 20≤groupHi (groupOf 20) ∧
    inputRate 20≤groupBar (groupOf 20) ∧ groupOf 20<23 := by
  exact IntInput.original_input_fact 20 (by decide +kernel)

/-- Retained source input21; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_21 :
    inputLo 21=N44.Data.pieceLo.getD 21 0 ∧
    inputHi 21=N44.Data.pieceHi.getD 21 0 ∧
    inputRate 21=(N44.Data.rates44.getD 21 []).getD 0 0 ∧
    groupLo (groupOf 21)≤ inputLo 21 ∧ inputHi 21≤groupHi (groupOf 21) ∧
    inputRate 21≤groupBar (groupOf 21) ∧ groupOf 21<23 := by
  exact IntInput.original_input_fact 21 (by decide +kernel)

/-- Retained source input22; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_22 :
    inputLo 22=N44.Data.pieceLo.getD 22 0 ∧
    inputHi 22=N44.Data.pieceHi.getD 22 0 ∧
    inputRate 22=(N44.Data.rates44.getD 22 []).getD 0 0 ∧
    groupLo (groupOf 22)≤ inputLo 22 ∧ inputHi 22≤groupHi (groupOf 22) ∧
    inputRate 22≤groupBar (groupOf 22) ∧ groupOf 22<23 := by
  exact IntInput.original_input_fact 22 (by decide +kernel)

/-- Retained source input23; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_23 :
    inputLo 23=N44.Data.pieceLo.getD 23 0 ∧
    inputHi 23=N44.Data.pieceHi.getD 23 0 ∧
    inputRate 23=(N44.Data.rates44.getD 23 []).getD 0 0 ∧
    groupLo (groupOf 23)≤ inputLo 23 ∧ inputHi 23≤groupHi (groupOf 23) ∧
    inputRate 23≤groupBar (groupOf 23) ∧ groupOf 23<23 := by
  exact IntInput.original_input_fact 23 (by decide +kernel)

/-- Retained source input24; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_24 :
    inputLo 24=N44.Data.pieceLo.getD 24 0 ∧
    inputHi 24=N44.Data.pieceHi.getD 24 0 ∧
    inputRate 24=(N44.Data.rates44.getD 24 []).getD 0 0 ∧
    groupLo (groupOf 24)≤ inputLo 24 ∧ inputHi 24≤groupHi (groupOf 24) ∧
    inputRate 24≤groupBar (groupOf 24) ∧ groupOf 24<23 := by
  exact IntInput.original_input_fact 24 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_20
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_20
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_21
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_21
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_22
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_22
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_23
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_23
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_24
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_24
