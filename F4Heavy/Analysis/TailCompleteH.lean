module

public import F4Heavy.Analysis.TailFinalOfGuards
public import F4Heavy.Analysis.TailGuardH01
public import F4Heavy.Analysis.TailGuardH02
public import F4Heavy.Analysis.TailGuardH03
public import F4Heavy.Analysis.TailGuardH04
public import F4Heavy.Analysis.TailGuardH05
public import F4Heavy.Analysis.TailGuardH06
public import F4Heavy.Analysis.TailGuardH07
public import F4Heavy.Analysis.TailGuardH08
public import F4Heavy.Analysis.TailGuardH09
public import F4Heavy.Analysis.TailGuardH10
public import F4Heavy.Analysis.TailGuardH11
public import F4Heavy.Analysis.TailGuardH12
public import F4Heavy.Analysis.TailGuardH13
public import F4Heavy.Analysis.TailGuardH14
public import F4Heavy.Analysis.TailGuardH15
public import F4Heavy.Analysis.TailGuardH16

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_H_all_guards (lam : ℝ) (hr : InRow .H lam) (i : Nat)
    (hi : 1 ≤ i) (hj : i ≤ 16) : 0 < tailGuard .H lam i := by
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail_guard_H_01_positive lam hr
  · exact tail_guard_H_02_positive lam hr
  · exact tail_guard_H_03_positive lam hr
  · exact tail_guard_H_04_positive lam hr
  · exact tail_guard_H_05_positive lam hr
  · exact tail_guard_H_06_positive lam hr
  · exact tail_guard_H_07_positive lam hr
  · exact tail_guard_H_08_positive lam hr
  · exact tail_guard_H_09_positive lam hr
  · exact tail_guard_H_10_positive lam hr
  · exact tail_guard_H_11_positive lam hr
  · exact tail_guard_H_12_positive lam hr
  · exact tail_guard_H_13_positive lam hr
  · exact tail_guard_H_14_positive lam hr
  · exact tail_guard_H_15_positive lam hr
  · exact tail_guard_H_16_positive lam hr

theorem tail_positive_H_complete : TailPositive .H := by
  exact tail_positive_of_guards .H tail_H_all_guards

end F4Heavy.Analysis
