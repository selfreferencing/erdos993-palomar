module

public import F4Heavy.Contract
public import F4Heavy.Analysis.EAllSupports
public import F4Heavy.Analysis.EUpperPayment
public import F4Heavy.Analysis.DFinal
public import F4Heavy.Analysis.HFinal

/-!
# The targets

Each statement below is proved here from the results of `F4Heavy/Analysis/`. They are `F4Unified.CompactHeavy r` from the
contract, for the four rows.
-/

@[expose] public section

namespace F4Heavy

open F4Unified

theorem compactHeavy_D : CompactHeavy .D := by
  exact Analysis.compactHeavy_D_proved

theorem compactHeavy_E1 : CompactHeavy .E1 := by
  exact Analysis.e_compactHeavy_of_support_lines .E1 (Or.inl rfl)
    Analysis.e1_child_support_lines

theorem compactHeavy_E2 : CompactHeavy .E2 := by
  exact Analysis.e_compactHeavy_of_support_lines .E2 (Or.inr rfl)
    Analysis.e2_child_support_lines

theorem compactHeavy_H : CompactHeavy .H := by
  exact Analysis.compactHeavy_H_proved

theorem compactHeavy_all : ∀ r, CompactHeavy r := by
  intro r
  cases r
  · exact compactHeavy_D
  · exact compactHeavy_E1
  · exact compactHeavy_E2
  · exact compactHeavy_H

end F4Heavy
