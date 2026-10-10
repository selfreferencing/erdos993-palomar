module

public import F4Heavy.Analysis.TailFinalOfGuards
public import F4Heavy.Analysis.TailGuardE101
public import F4Heavy.Analysis.TailGuardE102
public import F4Heavy.Analysis.TailGuardE103
public import F4Heavy.Analysis.TailGuardE104
public import F4Heavy.Analysis.TailGuardE105
public import F4Heavy.Analysis.TailGuardE106
public import F4Heavy.Analysis.TailGuardE107
public import F4Heavy.Analysis.TailGuardE108
public import F4Heavy.Analysis.TailGuardE109
public import F4Heavy.Analysis.TailGuardE110
public import F4Heavy.Analysis.TailGuardE111
public import F4Heavy.Analysis.TailGuardE112
public import F4Heavy.Analysis.TailGuardE113
public import F4Heavy.Analysis.TailGuardE114
public import F4Heavy.Analysis.TailGuardE115
public import F4Heavy.Analysis.TailGuardE116

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_E1_all_guards (lam : ℝ) (hr : InRow .E1 lam) (i : Nat)
    (hi : 1 ≤ i) (hj : i ≤ 16) : 0 < tailGuard .E1 lam i := by
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail_guard_E1_01_positive lam hr
  · exact tail_guard_E1_02_positive lam hr
  · exact tail_guard_E1_03_positive lam hr
  · exact tail_guard_E1_04_positive lam hr
  · exact tail_guard_E1_05_positive lam hr
  · exact tail_guard_E1_06_positive lam hr
  · exact tail_guard_E1_07_positive lam hr
  · exact tail_guard_E1_08_positive lam hr
  · exact tail_guard_E1_09_positive lam hr
  · exact tail_guard_E1_10_positive lam hr
  · exact tail_guard_E1_11_positive lam hr
  · exact tail_guard_E1_12_positive lam hr
  · exact tail_guard_E1_13_positive lam hr
  · exact tail_guard_E1_14_positive lam hr
  · exact tail_guard_E1_15_positive lam hr
  · exact tail_guard_E1_16_positive lam hr

theorem tail_positive_E1_complete : TailPositive .E1 := by
  exact tail_positive_of_guards .E1 tail_E1_all_guards

end F4Heavy.Analysis
