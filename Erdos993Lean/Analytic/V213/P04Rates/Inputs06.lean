module

public import Erdos993Lean.F4Fast.P04IntegerInputs

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

/-- Retained source input30; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_30 :
    inputLo 30=N44.Data.pieceLo.getD 30 0 ∧
    inputHi 30=N44.Data.pieceHi.getD 30 0 ∧
    inputRate 30=(N44.Data.rates44.getD 30 []).getD 0 0 ∧
    groupLo (groupOf 30)≤ inputLo 30 ∧ inputHi 30≤groupHi (groupOf 30) ∧
    inputRate 30≤groupBar (groupOf 30) ∧ groupOf 30<23 := by
  exact IntInput.original_input_fact 30 (by decide +kernel)

/-- Retained source input31; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_31 :
    inputLo 31=N44.Data.pieceLo.getD 31 0 ∧
    inputHi 31=N44.Data.pieceHi.getD 31 0 ∧
    inputRate 31=(N44.Data.rates44.getD 31 []).getD 0 0 ∧
    groupLo (groupOf 31)≤ inputLo 31 ∧ inputHi 31≤groupHi (groupOf 31) ∧
    inputRate 31≤groupBar (groupOf 31) ∧ groupOf 31<23 := by
  exact IntInput.original_input_fact 31 (by decide +kernel)

/-- Retained source input32; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_32 :
    inputLo 32=N44.Data.pieceLo.getD 32 0 ∧
    inputHi 32=N44.Data.pieceHi.getD 32 0 ∧
    inputRate 32=(N44.Data.rates44.getD 32 []).getD 0 0 ∧
    groupLo (groupOf 32)≤ inputLo 32 ∧ inputHi 32≤groupHi (groupOf 32) ∧
    inputRate 32≤groupBar (groupOf 32) ∧ groupOf 32<23 := by
  exact IntInput.original_input_fact 32 (by decide +kernel)

/-- Retained source input33; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_33 :
    inputLo 33=N44.Data.pieceLo.getD 33 0 ∧
    inputHi 33=N44.Data.pieceHi.getD 33 0 ∧
    inputRate 33=(N44.Data.rates44.getD 33 []).getD 0 0 ∧
    groupLo (groupOf 33)≤ inputLo 33 ∧ inputHi 33≤groupHi (groupOf 33) ∧
    inputRate 33≤groupBar (groupOf 33) ∧ groupOf 33<23 := by
  exact IntInput.original_input_fact 33 (by decide +kernel)

/-- Retained source input34; three exact custody equalities plus group containment and rate domination. -/
theorem input_facts_34 :
    inputLo 34=N44.Data.pieceLo.getD 34 0 ∧
    inputHi 34=N44.Data.pieceHi.getD 34 0 ∧
    inputRate 34=(N44.Data.rates44.getD 34 []).getD 0 0 ∧
    groupLo (groupOf 34)≤ inputLo 34 ∧ inputHi 34≤groupHi (groupOf 34) ∧
    inputRate 34≤groupBar (groupOf 34) ∧ groupOf 34<23 := by
  exact IntInput.original_input_fact 34 (by decide +kernel)


end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_30
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_30
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_31
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_31
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_32
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_32
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_33
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_33
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_34
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.input_facts_34
