module

import F4Heavy.Analysis.DHFormulaH35

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem hUW1V1_response_positive (lam x : ℝ) (hr : InRow .H lam)
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .H lam x 1 (parentLogUpper .H lam x) (hUpperSupportVertex lam 1) (hUpperSupportHeight lam 1) := by
  exact hUW1V1_primary_positive lam x hr hx

end F4Heavy.Analysis
