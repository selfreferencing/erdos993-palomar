module

import F4Heavy.Analysis.DHFormulaH28

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem hUW0V0_response_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x 1 (parentLogLower .H lam x) (hUpperSupportVertex lam 0) (hUpperSupportHeight lam 0) := by
  exact hUW0V0_primary_positive lam x hr hx

end F4Heavy.Analysis
