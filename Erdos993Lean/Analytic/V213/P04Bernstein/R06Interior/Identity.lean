module

public import Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.Integer

/-! Ported to the Lean module system for the Palomar registry. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

theorem reconstruction_checked :
    Bi.checkEq chart (fromBernstein n m coeff) = true := by
  exact integer_original_identity

end Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.reconstruction_checked
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.reconstruction_checked
