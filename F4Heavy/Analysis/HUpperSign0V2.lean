module

import F4Heavy.Analysis.DHFormulaH30

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem hUW0V2_response_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x 1 (parentLogLower .H lam x) (hUpperSupportVertex lam 2) (hUpperSupportHeight lam 2) := by
  exact hUW0V2_primary_positive lam x hr hx

end F4Heavy.Analysis
