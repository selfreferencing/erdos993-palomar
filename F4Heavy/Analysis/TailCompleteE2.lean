module

public import F4Heavy.Analysis.TailFinalOfGuards
public import F4Heavy.Analysis.TailGuardE201
public import F4Heavy.Analysis.TailGuardE202
public import F4Heavy.Analysis.TailGuardE203
public import F4Heavy.Analysis.TailGuardE204
public import F4Heavy.Analysis.TailGuardE205
public import F4Heavy.Analysis.TailGuardE206
public import F4Heavy.Analysis.TailGuardE207
public import F4Heavy.Analysis.TailGuardE208
public import F4Heavy.Analysis.TailGuardE209
public import F4Heavy.Analysis.TailGuardE210
public import F4Heavy.Analysis.TailGuardE211
public import F4Heavy.Analysis.TailGuardE212
public import F4Heavy.Analysis.TailGuardE213
public import F4Heavy.Analysis.TailGuardE214
public import F4Heavy.Analysis.TailGuardE215
public import F4Heavy.Analysis.TailGuardE216

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem tail_E2_all_guards (lam : ℝ) (hr : InRow .E2 lam) (i : Nat)
    (hi : 1 ≤ i) (hj : i ≤ 16) : 0 < tailGuard .E2 lam i := by
  have hcases : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tail_guard_E2_01_positive lam hr
  · exact tail_guard_E2_02_positive lam hr
  · exact tail_guard_E2_03_positive lam hr
  · exact tail_guard_E2_04_positive lam hr
  · exact tail_guard_E2_05_positive lam hr
  · exact tail_guard_E2_06_positive lam hr
  · exact tail_guard_E2_07_positive lam hr
  · exact tail_guard_E2_08_positive lam hr
  · exact tail_guard_E2_09_positive lam hr
  · exact tail_guard_E2_10_positive lam hr
  · exact tail_guard_E2_11_positive lam hr
  · exact tail_guard_E2_12_positive lam hr
  · exact tail_guard_E2_13_positive lam hr
  · exact tail_guard_E2_14_positive lam hr
  · exact tail_guard_E2_15_positive lam hr
  · exact tail_guard_E2_16_positive lam hr

theorem tail_positive_E2_complete : TailPositive .E2 := by
  exact tail_positive_of_guards .E2 tail_E2_all_guards

end F4Heavy.Analysis
