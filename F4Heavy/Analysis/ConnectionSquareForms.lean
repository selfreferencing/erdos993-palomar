module

public import F4Heavy.Analysis.PolynomialIdentity

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis

theorem connection_square_product (r c q u b s t : ℝ) :
    (r*(5*c^2))*u^2*q^6*b^6*s^2*t^2 =
      r*(5*(c*q^3*u*b^3*s*t)^2) := by
  ring

end F4Heavy.Analysis
