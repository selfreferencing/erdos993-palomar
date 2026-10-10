module

public import Erdos993Lean.Analytic.V213.FiberProfileLineNormal
public import Mathlib.Analysis.Convex.Deriv

/-!
Actual first and second derivatives of the rational line normal
form, and convexity on the entire closed root-line piece.
The later canonical data consumer discharges the second
derivative guards and binds the normal form to each D/E record.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

noncomputable def fiberProfileLinePrime (p2 p1 K L beta d0 t : ℝ) : ℝ :=
  2 * p2 * t + p1 - beta * K / (beta * t - d0) ^ 2 +
    beta * L / (1 + beta * t - d0) ^ 2

noncomputable def fiberProfileLineSecond (p2 K L beta d0 t : ℝ) : ℝ :=
  2 * p2 + 2 * beta ^ 2 * K / (beta * t - d0) ^ 3 -
    2 * beta ^ 2 * L / (1 + beta * t - d0) ^ 3

theorem fiber_profile_line_hasDerivAt (p2 p1 p0 K L beta d0 : ℝ) {t : ℝ}
    (hw : 0 < beta * t - d0) :
    HasDerivAt (fiberProfileLine p2 p1 p0 K L beta d0)
      (fiberProfileLinePrime p2 p1 K L beta d0 t) t := by
  have hw1 : 1 + beta * t - d0 ≠ 0 := by linarith only [hw]
  have hdw := ((hasDerivAt_id t).const_mul beta).sub_const d0
  have hdw1 := ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul beta)).sub_const d0
  have hq := ((hasDerivAt_id t).pow 2).const_mul p2
  have hl := (hasDerivAt_id t).const_mul p1
  have hk := (hasDerivAt_const t K).div hdw hw.ne'
  have hL := (hasDerivAt_const t L).div hdw1 hw1
  convert ((((hq.add hl).add_const p0).add hk).sub hL) using 1
  · funext x
    rfl
  · dsimp [fiberProfileLinePrime]
    ring

theorem fiber_profile_line_prime_hasDerivAt (p2 p1 K L beta d0 : ℝ) {t : ℝ}
    (hw : 0 < beta * t - d0) :
    HasDerivAt (fiberProfileLinePrime p2 p1 K L beta d0)
      (fiberProfileLineSecond p2 K L beta d0 t) t := by
  have hw1 : 1 + beta * t - d0 ≠ 0 := by linarith only [hw]
  have hdw := ((hasDerivAt_id t).const_mul beta).sub_const d0
  have hdw1 := ((hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul beta)).sub_const d0
  have hl := ((hasDerivAt_id t).const_mul (2 * p2)).add_const p1
  have hk := (hasDerivAt_const t (beta * K)).div (hdw.pow 2) (pow_ne_zero _ hw.ne')
  have hL := (hasDerivAt_const t (beta * L)).div (hdw1.pow 2) (pow_ne_zero _ hw1)
  convert (hl.sub hk).add hL using 1
  · funext x
    rfl
  · dsimp [fiberProfileLineSecond]
    field_simp [hw.ne',hw1]
    ring

theorem fiber_profile_line_convex {p2 p1 p0 K L beta d0 l h : ℝ}
    (hw : ∀ t ∈ Icc l h, 0 < beta * t - d0)
    (hsecond : ∀ t ∈ Icc l h, 0 ≤ fiberProfileLineSecond p2 K L beta d0 t) :
    ConvexOn ℝ (Icc l h) (fiberProfileLine p2 p1 p0 K L beta d0) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fiberProfileLinePrime p2 p1 K L beta d0)
    (f'' := fiberProfileLineSecond p2 K L beta d0) (convex_Icc _ _)
  · intro t ht
    exact (fiber_profile_line_hasDerivAt _ _ _ _ _ _ _ (hw t ht)).continuousAt.continuousWithinAt
  · intro t ht
    exact (fiber_profile_line_hasDerivAt _ _ _ _ _ _ _ (hw t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact (fiber_profile_line_prime_hasDerivAt _ _ _ _ _ _ (hw t (interior_subset ht))).hasDerivWithinAt
  · intro t ht
    exact hsecond t (interior_subset ht)

theorem fiber_profile_D_second_identity {cf df rho kappa m s delta alpha beta t u : ℝ}
    (hm : m ≠ 0) :
    fiberProfileLineSecond (fiberProfileDP2 rho kappa m s delta beta u)
      (fiberProfileDK cf df rho kappa m s alpha beta u) (cf / m) beta (alpha - 1) t =
    2 * beta * fiberProfileB1 rho kappa s u - 9 - 2 * delta * m * u ^ 2 +
      2 * beta ^ 2 * ((fiberProfileB0 rho kappa m s u +
        fiberProfileB1 rho kappa s u * (alpha - 1) / beta + (cf + df - 11 / 10) / m) /
          (beta * t - (alpha - 1)) ^ 3 - cf / (m * (1 + beta * t - (alpha - 1)) ^ 3)) := by
  unfold fiberProfileLineSecond fiberProfileDP2 fiberProfileDK
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem fiber_profile_E_second_identity (alpha beta t u : ℝ) (hbeta : beta ≠ 0) :
    fiberProfileLineSecond (beta * fiberProfileEB0 u - 9 / 2 - 38 * u ^ 2)
      ((alpha - 1) * fiberProfileEB0 u / beta) 0 beta (alpha - 1) t =
      2 * beta * fiberProfileEB0 u + 2 * beta * (alpha - 1) * fiberProfileEB0 u /
        (beta * t - (alpha - 1)) ^ 3 - 76 * u ^ 2 - 9 := by
  unfold fiberProfileLineSecond
  simp only [mul_zero,zero_div,sub_zero]
  field_simp [hbeta]
  ring

end Erdos993Lean.Analytic.V213
