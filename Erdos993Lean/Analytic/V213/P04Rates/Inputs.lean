module

public import Erdos993Lean.Analytic.V213.P04Rates.Inputs00
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs01
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs02
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs03
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs04
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs05
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs06
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs07
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs08
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs09
public import Erdos993Lean.Analytic.V213.P04Rates.Inputs10

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

theorem all_input_facts (i : Nat) (hi : i<55) :
    inputLo i=N44.Data.pieceLo.getD i 0 ∧
    inputHi i=N44.Data.pieceHi.getD i 0 ∧
    inputRate i=(N44.Data.rates44.getD i []).getD 0 0 ∧
    groupLo (groupOf i)≤ inputLo i ∧ inputHi i≤groupHi (groupOf i) ∧
    inputRate i≤groupBar (groupOf i) ∧ groupOf i<23 := by
  interval_cases i <;> first
  | exact input_facts_00
  | exact input_facts_01
  | exact input_facts_02
  | exact input_facts_03
  | exact input_facts_04
  | exact input_facts_05
  | exact input_facts_06
  | exact input_facts_07
  | exact input_facts_08
  | exact input_facts_09
  | exact input_facts_10
  | exact input_facts_11
  | exact input_facts_12
  | exact input_facts_13
  | exact input_facts_14
  | exact input_facts_15
  | exact input_facts_16
  | exact input_facts_17
  | exact input_facts_18
  | exact input_facts_19
  | exact input_facts_20
  | exact input_facts_21
  | exact input_facts_22
  | exact input_facts_23
  | exact input_facts_24
  | exact input_facts_25
  | exact input_facts_26
  | exact input_facts_27
  | exact input_facts_28
  | exact input_facts_29
  | exact input_facts_30
  | exact input_facts_31
  | exact input_facts_32
  | exact input_facts_33
  | exact input_facts_34
  | exact input_facts_35
  | exact input_facts_36
  | exact input_facts_37
  | exact input_facts_38
  | exact input_facts_39
  | exact input_facts_40
  | exact input_facts_41
  | exact input_facts_42
  | exact input_facts_43
  | exact input_facts_44
  | exact input_facts_45
  | exact input_facts_46
  | exact input_facts_47
  | exact input_facts_48
  | exact input_facts_49
  | exact input_facts_50
  | exact input_facts_51
  | exact input_facts_52
  | exact input_facts_53
  | exact input_facts_54

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.all_input_facts
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.PrintedRates.all_input_facts
