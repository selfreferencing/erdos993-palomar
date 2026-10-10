module

import F4Heavy.Analysis.DHFormulaD08

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem dUW1V2_response_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x 1 (parentLogUpper .D lam x) (dSupportVertex lam 2) (dSupportHeight lam 2) := by
  exact dUW1V2_primary_positive lam x hr hx

end F4Heavy.Analysis
