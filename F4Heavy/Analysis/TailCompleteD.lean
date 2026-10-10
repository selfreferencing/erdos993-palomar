module

public import F4Heavy.Analysis.TailFinalOfGuards
public import F4Heavy.Analysis.TailGuardD01
public import F4Heavy.Analysis.TailGuardD02
public import F4Heavy.Analysis.TailGuardD03
public import F4Heavy.Analysis.TailGuardD04
public import F4Heavy.Analysis.TailGuardD05
public import F4Heavy.Analysis.TailGuardD06
public import F4Heavy.Analysis.TailGuardD07
public import F4Heavy.Analysis.TailGuardD08
public import F4Heavy.Analysis.TailGuardD09
public import F4Heavy.Analysis.TailGuardD10
public import F4Heavy.Analysis.TailGuardD11
public import F4Heavy.Analysis.TailGuardD12
public import F4Heavy.Analysis.TailGuardD13
public import F4Heavy.Analysis.TailGuardD14
public import F4Heavy.Analysis.TailGuardD15
public import F4Heavy.Analysis.TailGuardD16

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_D_all_guards (lam : ℝ) (hr : InRow .D lam) (i : Nat)
    (hi : 1 ≤ i) (hj : i ≤ 16) : 0 < tailGuard .D lam i := by
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail_guard_D_01_positive lam hr
  · exact tail_guard_D_02_positive lam hr
  · exact tail_guard_D_03_positive lam hr
  · exact tail_guard_D_04_positive lam hr
  · exact tail_guard_D_05_positive lam hr
  · exact tail_guard_D_06_positive lam hr
  · exact tail_guard_D_07_positive lam hr
  · exact tail_guard_D_08_positive lam hr
  · exact tail_guard_D_09_positive lam hr
  · exact tail_guard_D_10_positive lam hr
  · exact tail_guard_D_11_positive lam hr
  · exact tail_guard_D_12_positive lam hr
  · exact tail_guard_D_13_positive lam hr
  · exact tail_guard_D_14_positive lam hr
  · exact tail_guard_D_15_positive lam hr
  · exact tail_guard_D_16_positive lam hr

theorem tail_positive_D_complete : TailPositive .D := by
  exact tail_positive_of_guards .D tail_D_all_guards

end F4Heavy.Analysis

