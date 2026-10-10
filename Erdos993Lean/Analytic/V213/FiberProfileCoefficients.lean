module

public import Erdos993Lean.Analytic.V213.FiberProfileDefinitions

/-!
The literal quadratic coefficient formulas at a fixed endpoint.
They are identities of the actual Eq94/95 envelopes for every real u,
including both sign possibilities for the quadratic coefficient.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberProfileDConstant (cf df m b beta t a : ℝ) : ℝ :=
  fiberProfileF t a + b + beta * (t - 1) + fiberProfileC cf df a / m

noncomputable def fiberProfileDLinear (rho m s t a : ℝ) : ℝ :=
  2 * fiberProfileG0 a * (m * t + 2 + s ^ 2) / (s * rho * m)

noncomputable def fiberProfileDQuadratic (rho kappa m delta t a : ℝ) : ℝ :=
  (m * t + 2) / m * (kappa * fiberProfileG0 a / rho + delta - delta * (m * t + 2))

noncomputable def fiberProfileELinear (t a : ℝ) : ℝ :=
  97 * t * fiberProfileG0 a / (140 * (63 / 100))

noncomputable def fiberProfileEQuadratic (t a : ℝ) : ℝ :=
  t * ((17 / 6) * fiberProfileG0 a / (63 / 100) + 1 - 2 * (19 * t + 2))

theorem fiber_profile_D_polynomial (cf df rho kappa m s delta b beta t u a : ℝ) :
    fiberProfileD cf df rho kappa m s delta b beta t u a =
      fiberProfileDConstant cf df m b beta t a + fiberProfileDLinear rho m s t a * u +
        fiberProfileDQuadratic rho kappa m delta t a * u ^ 2 := by
  rfl

theorem fiber_profile_E_polynomial (t u a : ℝ) :
    fiberProfileE t u a = fiberProfileF t a + fiberProfileELinear t a * u +
      fiberProfileEQuadratic t a * u ^ 2 := by
  rfl

end Erdos993Lean.Analytic.V213
