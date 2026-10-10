module

public import Erdos993Lean.Analytic.V213.FiberAffineMassMinorant
public import Erdos993Lean.Analytic.V213.FiberAffineBranches
public import Erdos993Lean.Analytic.V213.FiberAffinePolynomialBounds

/-!
Literal H_beta is a lower bound for the actual unnormalized affine
excess on every t>=3/4,w in[0,3/2]. Eq85, exp>=1+x, the nonnegative
minorant and B>=t are consumed with their signs proved. No H/curvature
or binomial premise is hidden in the resulting actual-fiber theorem.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberAffineLinearMinorant (t w : ℝ) : ℝ :=
  w + t ^ (-(5 / 2 : ℝ)) * (fiberAffineG t - w) * fiberAffineC w

theorem fiber_affine_linear_minorant_nonneg {t w : ℝ}
    (ht : 3 / 4 ≤ t) (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    0 ≤ fiberAffineLinearMinorant t w := by
  have ht0 : 0 ≤ t := by linarith only [ht]
  unfold fiberAffineLinearMinorant
  exact add_nonneg hw0 (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht0 _)
    (fiber_affine_g_window (by linarith only [ht]) hwh)) (fiber_affine_C_pos hwh).le)

theorem fiber_affine_linear_minorant_le {t w : ℝ}
    (ht : 3 / 4 ≤ t) (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    fiberAffineLinearMinorant t w ≤ w + t ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG t - w) * Real.exp (3 / 10 - (21 / 40 : ℝ) * w) := by
  have he : fiberAffineC w ≤ Real.exp (3 / 10 - (21 / 40 : ℝ) * w) := by
    unfold fiberAffineC
    convert Real.add_one_le_exp (3 / 10 - (21 / 40 : ℝ) * w) using 1 <;> ring
  have hp : 0 ≤ t ^ (-(5 / 2 : ℝ)) * (fiberAffineG t - w) :=
    mul_nonneg (Real.rpow_nonneg (by linarith only [ht]) _) (fiber_affine_g_window (by linarith only [ht]) hwh)
  unfold fiberAffineLinearMinorant
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he hp)

theorem fiber_affine_support_identity {t : ℝ} (ht : 0 < t) (beta w : ℝ) :
    t * fiberAffineLinearMinorant t w - (fiberPsi t + 2 / 5 + beta * (t - 1)) =
      fiberAffineSupport beta t w := by
  have h3 : t * t ^ (-(5 / 2 : ℝ)) = t ^ (-(3 / 2 : ℝ)) := by
    calc
      _ = t ^ (1 : ℝ) * t ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_one]
      _ = t ^ ((1 : ℝ) - 5 / 2) := by rw [sub_eq_add_neg, Real.rpow_add ht]
      _ = _ := by norm_num
  have h1 : t ^ 2 * t ^ (-(5 / 2 : ℝ)) = t ^ (-(1 / 2 : ℝ)) := by
    calc
      _ = t ^ (2 : ℝ) * t ^ (-(5 / 2 : ℝ)) := by rw [Real.rpow_two]
      _ = t ^ ((2 : ℝ) - 5 / 2) := by rw [sub_eq_add_neg, Real.rpow_add ht]
      _ = _ := by norm_num
  unfold fiberAffineLinearMinorant fiberAffineG fiberPsi fiberAffineSupport
  have he : t * (w + t ^ (-(5 / 2 : ℝ)) * (641 / 625 + (128 / 125) * t - w) * fiberAffineC w) =
      t * w + fiberAffineC w * ((641 / 625 - w) * (t * t ^ (-(5 / 2 : ℝ))) +
        (128 / 125) * (t ^ 2 * t ^ (-(5 / 2 : ℝ)))) := by ring
  rw [he,h3,h1]
  ring

theorem fiber_affine_support_actual {q mu b beta : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (hb : b ≤ 2 / 5) (M : ℕ) (j : ℤ)
    (ht : 3 / 4 ≤ (M : ℝ) / mu) (hw : fiberSquareOffset q M j ≤ 3 / 2) :
    fiberAffineSupport beta ((M : ℝ) / mu) (fiberSquareOffset q M j) ≤
      fiberF q mu M j - (fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1)) := by
  have hm0 : 0 < mu := by linarith only [hmu]
  have ht0 : 0 < (M : ℝ) / mu := by linarith only [ht]
  have hM := fiber_affine_width32 hmu ht
  have hw0 := fiber_square_offset_nonneg (by linarith : 0 < q) (by linarith : q < 1) M j
  have hl := (fiber_affine_linear_minorant_le ht hw0 hw).trans
    (fiber_affine_eq85_second hM hq0 hqh hrl hmu (by linarith only [ht]) j hw)
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hF := (le_div_iff₀ hB).mp hl
  have hBt : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
    div_le_div_of_nonneg_right (by linarith) hm0.le
  have hprod := mul_le_mul_of_nonneg_right hBt (fiber_affine_linear_minorant_nonneg ht hw0 hw)
  have he := fiber_affine_support_identity ht0 beta (fiberSquareOffset q M j)
  nlinarith only [hF,hprod,he,hb]

end Erdos993Lean.Analytic.V213
