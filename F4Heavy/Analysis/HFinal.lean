module

public import Mathlib.Tactic.FinCases

public import F4Heavy.Analysis.HUpperSign0V0
public import F4Heavy.Analysis.HUpperSign0V1
public import F4Heavy.Analysis.HUpperSign0V2
public import F4Heavy.Analysis.HUpperSign0V3
public import F4Heavy.Analysis.HUpperSign0V4
public import F4Heavy.Analysis.HUpperSign1V0
public import F4Heavy.Analysis.HUpperSign1V1
public import F4Heavy.Analysis.HUpperSign1V2
public import F4Heavy.Analysis.HUpperSign1V3
public import F4Heavy.Analysis.HUpperSign1V4
public import F4Heavy.Analysis.HLowerPrimaryApplications

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem h_upper_primary_positive (lam x z : ℝ) (hr : InRow .H lam)
    (hx0 : (1/4 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hz : z = parentLogLower .H lam x ∨ z = parentLogUpper .H lam x) (i : Fin 5) :
    0 < dhWFormula .H lam x 1 z (hUpperSupportVertex lam i) (hUpperSupportHeight lam i) := by
  rcases hz with rfl | rfl
  · fin_cases i
    · exact hUW0V0_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW0V1_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW0V2_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW0V3_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW0V4_response_positive lam x hr ⟨hx0, hx1⟩
  · fin_cases i
    · exact hUW1V0_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW1V1_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW1V2_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW1V3_response_positive lam x hr ⟨hx0, hx1⟩
    · exact hUW1V4_response_positive lam x hr ⟨hx0, hx1⟩

theorem compactHeavy_H_proved : CompactHeavy .H := by
  exact h_compactHeavy_of_upper_primary h_upper_primary_positive

end F4Heavy.Analysis
