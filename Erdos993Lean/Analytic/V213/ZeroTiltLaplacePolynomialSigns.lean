module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceSignPolynomials

/-! Exact finite interface for the ten printed closed rectangles.
This structure is not inhabited here. Its fields are the five literal
polynomial families at the actual rate switch, with the full u interval. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace

structure CurrentPolynomialSigns : Prop where
  minus : ∀ q : ℝ, QDomain q → 0<polyMinus q
  plus : ∀ q : ℝ, QDomain q → 0<polyPlus q
  interior : ∀ q u : ℝ, QDomain q → 0≤u → u≤1 → 0<polyI q u (delta q)
  leafSlope : ∀ q u : ℝ, QDomain q → 0≤u → u≤1 → 0<polyJ q u (delta q)
  leaf : ∀ q : ℝ, QDomain q → 0≤polyE q (delta q)

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.CurrentPolynomialSigns

#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.CurrentPolynomialSigns
