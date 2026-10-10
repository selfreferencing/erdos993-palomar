module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.Integer

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

theorem reconstruction_checked :
    Bi.checkEq chart (fromBernstein n m coeff) = true := by
  exact integer_original_identity

end Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus

#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.reconstruction_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.reconstruction_checked
