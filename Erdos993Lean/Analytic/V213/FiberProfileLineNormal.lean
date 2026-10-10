module

public import Erdos993Lean.Analytic.V213.FiberProfileDefinitions

/-!
Full rational normal forms of the actual D/E profiles along the
printed root line a=alpha-beta*t. Every coefficient is a displayed
formula in the original record parameters.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberProfileLine (p2 p1 p0 K L beta d0 t : ℝ) : ℝ :=
  p2 * t ^ 2 + p1 * t + p0 + K / (beta * t - d0) - L / (1 + beta * t - d0)

noncomputable def fiberProfileDP2 (rho kappa m s delta beta u : ℝ) : ℝ :=
  beta * fiberProfileB1 rho kappa s u - 9 / 2 - delta * m * u ^ 2

noncomputable def fiberProfileDP1 (rho kappa m s delta targetBeta alpha beta u : ℝ) : ℝ :=
  beta * fiberProfileB0 rho kappa m s u - (alpha + 1) * fiberProfileB1 rho kappa s u +
    6 * beta / m + 9 + targetBeta - 3 * delta * u ^ 2

noncomputable def fiberProfileDP0 (df rho kappa m s delta b targetBeta alpha beta u : ℝ) : ℝ :=
  -(alpha + 1) * fiberProfileB0 rho kappa m s u + fiberProfileB1 rho kappa s u / beta +
    (-6 * alpha - 2 - df + 11 / 10) / m - 9 / 2 + b - targetBeta - 2 * delta * u ^ 2 / m

noncomputable def fiberProfileDK (cf df rho kappa m s alpha beta u : ℝ) : ℝ :=
  fiberProfileB0 rho kappa m s u + fiberProfileB1 rho kappa s u * (alpha - 1) / beta +
    (cf + df - 11 / 10) / m

theorem fiber_profile_D_line_normal {cf df rho kappa m s delta b targetBeta alpha beta t u : ℝ}
    (hr : rho ≠ 0) (hm : m ≠ 0) (hs : s ≠ 0) (hbeta : beta ≠ 0)
    (ha : alpha - beta * t < 1) :
    fiberProfileD cf df rho kappa m s delta b targetBeta t u (alpha - beta * t) =
      fiberProfileLine (fiberProfileDP2 rho kappa m s delta beta u)
        (fiberProfileDP1 rho kappa m s delta targetBeta alpha beta u)
        (fiberProfileDP0 df rho kappa m s delta b targetBeta alpha beta u)
        (fiberProfileDK cf df rho kappa m s alpha beta u) (cf / m) beta (alpha - 1) t := by
  have hw : beta * t - (alpha - 1) ≠ 0 := by linarith only [ha]
  have hw1 : 1 + beta * t - (alpha - 1) ≠ 0 := by linarith only [ha]
  have hw' : 1 + beta * t - alpha ≠ 0 := by linarith only [ha]
  have hw1' : 2 + beta * t - alpha ≠ 0 := by linarith only [ha]
  rw [fiber_profile_D_normal hr hm hs,
    fiber_profile_G0_reciprocal (by linarith only [ha]),
    fiber_profile_C_reciprocal (by linarith only [ha]) (by linarith only [ha])]
  unfold fiberProfileLine fiberProfileDP2 fiberProfileDP1 fiberProfileDP0 fiberProfileDK
  have h1 : 1 - (alpha - beta * t) = beta * t - (alpha - 1) := by ring
  have h2 : 2 - (alpha - beta * t) = 1 + beta * t - (alpha - 1) := by ring
  rw [h1,h2]
  field_simp [hm,hbeta,hw,hw1,hw',hw1']
  ring

theorem fiber_profile_E_line_normal {alpha beta t u : ℝ} (hbeta : beta ≠ 0)
    (ha : alpha - beta * t < 1) :
    fiberProfileE t u (alpha - beta * t) =
      fiberProfileLine (beta * fiberProfileEB0 u - 9 / 2 - 38 * u ^ 2)
        (-(alpha + 1) * fiberProfileEB0 u + 9 - 3 * u ^ 2)
        (fiberProfileEB0 u / beta - 9 / 2)
        ((alpha - 1) * fiberProfileEB0 u / beta) 0 beta (alpha - 1) t := by
  have hw : beta * t - (alpha - 1) ≠ 0 := by linarith only [ha]
  have hw' : 1 + beta * t - alpha ≠ 0 := by linarith only [ha]
  rw [fiber_profile_E_normal,fiber_profile_G0_reciprocal (by linarith only [ha])]
  unfold fiberProfileLine
  have h1 : 1 - (alpha - beta * t) = beta * t - (alpha - 1) := by ring
  rw [h1]
  simp only [zero_div,sub_zero]
  field_simp [hbeta,hw,hw']
  linear_combination 2 * fiberProfileEB0 u * (mul_inv_cancel₀ hw')

end Erdos993Lean.Analytic.V213
