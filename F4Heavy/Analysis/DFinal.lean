module

public import F4Heavy.Analysis.DUpperSign0V0
public import F4Heavy.Analysis.DUpperSign0V1
public import F4Heavy.Analysis.DUpperSign0V2
public import F4Heavy.Analysis.DUpperSign0V3
public import F4Heavy.Analysis.DUpperSign1V0
public import F4Heavy.Analysis.DUpperSign1V1
public import F4Heavy.Analysis.DUpperSign1V2
public import F4Heavy.Analysis.DUpperSign1V3
public import F4Heavy.Analysis.DLowerPrimaryApplications

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem d_upper_primary_positive (lam x z : ℝ) (hr : InRow .D lam)
    (hx0 : (5/16 : ℝ) ≤ x) (hx1 : x ≤ 1)
    (hz : z = parentLogLower .D lam x ∨ z = parentLogUpper .D lam x) (i : Fin 4) :
    0 < dhWFormula .D lam x 1 z (dSupportVertex lam i) (dSupportHeight lam i) := by
  rcases hz with rfl | rfl
  · fin_cases i
    · exact dUW0V0_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW0V1_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW0V2_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW0V3_response_positive lam x hr ⟨hx0, hx1⟩
  · fin_cases i
    · exact dUW1V0_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW1V1_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW1V2_response_positive lam x hr ⟨hx0, hx1⟩
    · exact dUW1V3_response_positive lam x hr ⟨hx0, hx1⟩

theorem compactHeavy_D_proved : CompactHeavy .D := by
  exact d_compactHeavy_of_upper_primary d_upper_primary_positive

end F4Heavy.Analysis
