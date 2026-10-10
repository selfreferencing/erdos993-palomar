module

import F4Heavy.Analysis.DHFormulaD01

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHSupportGeometry

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified F4Heavy.Finite

theorem dUW0V0_response_positive (lam x : ℝ) (hr : InRow .D lam)
    (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    0 < dhWFormula .D lam x 1 (parentLogLower .D lam x) (dSupportVertex lam 0) (dSupportHeight lam 0) := by
  exact dUW0V0_primary_positive lam x hr hx

end F4Heavy.Analysis
