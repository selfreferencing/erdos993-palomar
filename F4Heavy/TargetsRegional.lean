module

public import F4Heavy.Analysis.LeafDiscriminantD
public import F4Heavy.Analysis.LeafDiscriminantE1
public import F4Heavy.Analysis.LeafDiscriminantE2
public import F4Heavy.Analysis.LeafDiscriminantH

public import F4Heavy.Analysis.TailCompleteH

public import F4Heavy.Analysis.TailCompleteE2

public import F4Heavy.Contract
public import F4Heavy.Analysis.CapFinalEH
public import F4Heavy.Analysis.CapFinalD
public import F4Heavy.Analysis.TailCompleteD
public import F4Heavy.Analysis.TailCompleteE1

/-!
# The regional targets: fixed-parent cap, tail and leaf

Each statement below is proved here from the results of `F4Heavy/Analysis/`. They are `F4Unified.FixedParentCap r`,
`F4Unified.TailPositive r` and `F4Unified.LeafPositive r` from the contract, for the four rows.
-/

@[expose] public section

namespace F4Heavy

open F4Unified

theorem fixedParentCap_D : FixedParentCap .D := by
  exact Analysis.fixedParentCap_D_complete

theorem fixedParentCap_E1 : FixedParentCap .E1 := by
  exact Analysis.fixedParentCap_nonD .E1 (by decide)

theorem fixedParentCap_E2 : FixedParentCap .E2 := by
  exact Analysis.fixedParentCap_nonD .E2 (by decide)

theorem fixedParentCap_H : FixedParentCap .H := by
  exact Analysis.fixedParentCap_nonD .H (by decide)

theorem fixedParentCap_all : ∀ r, FixedParentCap r := by
  intro r
  cases r
  · exact fixedParentCap_D
  · exact fixedParentCap_E1
  · exact fixedParentCap_E2
  · exact fixedParentCap_H

theorem tailPositive_D : TailPositive .D := by
  exact Analysis.tail_positive_D_complete

theorem tailPositive_E1 : TailPositive .E1 := by
  exact Analysis.tail_positive_E1_complete

theorem tailPositive_E2 : TailPositive .E2 := by
  exact Analysis.tail_positive_E2_complete

theorem tailPositive_H : TailPositive .H := by
  exact Analysis.tail_positive_H_complete

theorem tailPositive_all : ∀ r, TailPositive r := by
  intro r
  cases r
  · exact tailPositive_D
  · exact tailPositive_E1
  · exact tailPositive_E2
  · exact tailPositive_H

theorem leafPositive_D : LeafPositive .D := by
  exact Analysis.leafPositive_D_proved

theorem leafPositive_E1 : LeafPositive .E1 := by
  exact Analysis.leafPositive_E1_proved

theorem leafPositive_E2 : LeafPositive .E2 := by
  exact Analysis.leafPositive_E2_proved

theorem leafPositive_H : LeafPositive .H := by
  exact Analysis.leafPositive_H_proved

theorem leafPositive_all : ∀ r, LeafPositive r := by
  intro r
  cases r
  · exact leafPositive_D
  · exact leafPositive_E1
  · exact leafPositive_E2
  · exact leafPositive_H

end F4Heavy
