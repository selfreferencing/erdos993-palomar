module

public import Erdos993Lean.Analytic.V213.FiberAffineExponent
public import Erdos993Lean.Analytic.V213.FiberLowerBranches

/-!
The actual Eq75 AM--GM lower minorant is rewritten through the printed Y.
Its whole closed xi monotonicity is consumed, and g_*(t) is linked to the
actual width M, mean mu and shifted N=M+2. The two Eq85 tests retain all
integer ranks and discharge support/window guards through C103.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_affine_g_lower {N t mu : ℝ} (hmu : 40 ≤ mu) (ht : 0 ≤ t)
    (hN : N = mu * t + 2) :
    fiberAffineG t ≤ 1 + (16 / 625 : ℝ) * fiberAffineH N := by
  have hn : 0 < N := by rw [hN]; positivity
  have hi : 0 ≤ 1 / N := by positivity
  have hp : 0 ≤ (mu - 40) * t := mul_nonneg (by linarith only [hmu]) ht
  unfold fiberAffineG fiberAffineH
  rw [hN] at hi ⊢
  nlinarith only [hp,hi]

theorem fiber_affine_g_window {t w : ℝ} (ht : 1 / 2 ≤ t) (hw : w ≤ 3 / 2) :
    0 ≤ fiberAffineG t - w := by
  unfold fiberAffineG
  linarith only [ht,hw]

theorem fiber_affine_linear_Y (q mu : ℝ) (M : ℕ) (j : ℤ) :
    fiberLowerMassLinearGain q mu M j (3 / 2) =
      fiberSquareOffset q M j + ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
        Real.exp (V22.rho ((M : ℝ) + 2) * (1 - fiberSquareOffset q M j) / 2 -
          ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
          fiberMassError ((M : ℝ) + 2) (fiberSkew q) (3 / 2)) *
        fiberAffineY ((M : ℝ) + 2) (fiberSquareOffset q M j)
          (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) := by
  unfold fiberLowerMassLinearGain fiberLowerMassWeight fiberAffineY fiberAffineH fiberAffineK
  congr 1
  rw [show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring]
  ring

theorem fiber_affine_minorant {M : ℕ} (hM : 20 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (ht : 1 / 2 ≤ (M : ℝ) / mu) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ 3 / 2) :
    fiberSquareOffset q M j + ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG ((M : ℝ) / mu) - fiberSquareOffset q M j) *
      Real.exp (fiberAffineExponent ((M : ℝ) + 2) (fiberSkew q) (fiberSquareOffset q M j)) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hN : (22 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 22 ≤ M + 2)
  have hN0 : 0 < (M : ℝ) + 2 := by positivity
  have hm0 : 0 < mu := by linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith only [hqh]
  have hw0 := fiber_square_offset_nonneg (by linarith : 0 < q) (by linarith : q < 1) M j
  have hg := fiber_affine_gamma_lower hN hrl hrh
  have hb := fiber_bonus_current_formula (by linarith : 0 < q) (by linarith : q < 1) M
  have hWg : (3 / 2 : ℝ) ≤ fiberBonus q M := by
    rw [hb]
    have hgf := fiber_affine_gamma_formula hN hrl hrh
    unfold fiberAffineH at hgf
    rw [←hgf]
    exact hg.2.le
  have hl := fiber_lower_mass_linear_gain_used_windows (by omega : 12 ≤ M) hq0 hqh hm0
    (by norm_num : (1 : ℝ) ≤ 3 / 2) (by norm_num : (3 / 2 : ℝ) ≤ 3 / 2) j hw hWg
  rw [fiber_affine_linear_Y] at hl
  have hy := fiber_affine_Y_at_skew_lower hN hw0 hw hrl hrh
  have hbase : 0 ≤ ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      Real.exp (V22.rho ((M : ℝ) + 2) * (1 - fiberSquareOffset q M j) / 2 -
          ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
          fiberMassError ((M : ℝ) + 2) (fiberSkew q) (3 / 2)) := by positivity
  have hyg := mul_le_mul_of_nonneg_left hy hbase
  have hnEq : (M : ℝ) + 2 = mu * ((M : ℝ) / mu) + 2 := by field_simp [hm0.ne']
  have hgg := fiber_affine_g_lower hmu (by linarith only [ht]) hnEq
  have hcoeff := sub_le_sub_right hgg (fiberSquareOffset q M j)
  have hpow : 0 ≤ ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) := by positivity
  have hepow : 0 ≤ Real.exp (fiberAffineExponent ((M : ℝ) + 2) (fiberSkew q)
      (fiberSquareOffset q M j)) := Real.exp_nonneg _
  have heq : ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      Real.exp (V22.rho ((M : ℝ) + 2) * (1 - fiberSquareOffset q M j) / 2 -
          ((77 / 20 : ℝ) + 10 / (M : ℝ)) / ((M : ℝ) + 3) -
          fiberMassError ((M : ℝ) + 2) (fiberSkew q) (3 / 2)) *
      fiberAffineY ((M : ℝ) + 2) (fiberSquareOffset q M j) (4 / 25) =
      ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
        (1 + (16 / 625 : ℝ) * fiberAffineH ((M : ℝ) + 2) - fiberSquareOffset q M j) *
        Real.exp (fiberAffineExponent ((M : ℝ) + 2) (fiberSkew q) (fiberSquareOffset q M j)) := by
    unfold fiberAffineY fiberAffineExponent
    rw [show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring,
      show ((M : ℝ) + 2) - 2 = (M : ℝ) by ring]
    simp only [neg_div, Real.exp_sub, Real.exp_neg]
    norm_num only
    ring
  rw [heq] at hyg
  have hg2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff hpow) hepow
  exact (add_le_add le_rfl (hg2.trans hyg)).trans hl

theorem fiber_affine_eq85_first {M : ℕ} (hM : 20 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (ht : 1 / 2 ≤ (M : ℝ) / mu) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ 3 / 2) :
    fiberSquareOffset q M j + ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG ((M : ℝ) / mu) - fiberSquareOffset q M j) *
      Real.exp (1 / 5 - (8 / 15 : ℝ) * fiberSquareOffset q M j) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hN : (22 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 22 ≤ M + 2)
  have hr0 : 0 ≤ fiberSkew q := by linarith only [hrl]
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith only [hqh]
  have hw0 := fiber_square_offset_nonneg (by linarith : 0 < q) (by linarith : q < 1) M j
  have he := Real.exp_le_exp.mpr (fiber_affine_exponent22 hN hr0 hrh hw0)
  have hc : 0 ≤ ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG ((M : ℝ) / mu) - fiberSquareOffset q M j) :=
    mul_nonneg (by positivity) (fiber_affine_g_window ht hw)
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hc)).trans
    (fiber_affine_minorant hM hq0 hqh hrl hmu ht j hw)

theorem fiber_affine_eq85_second {M : ℕ} (hM : 30 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hrl : 4 / 25 ≤ fiberSkew q)
    (hmu : 40 ≤ mu) (ht : 1 / 2 ≤ (M : ℝ) / mu) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ 3 / 2) :
    fiberSquareOffset q M j + ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG ((M : ℝ) / mu) - fiberSquareOffset q M j) *
      Real.exp (3 / 10 - (21 / 40 : ℝ) * fiberSquareOffset q M j) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hN : (32 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 32 ≤ M + 2)
  have hr0 : 0 ≤ fiberSkew q := by linarith only [hrl]
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith only [hqh]
  have hw0 := fiber_square_offset_nonneg (by linarith : 0 < q) (by linarith : q < 1) M j
  have he := Real.exp_le_exp.mpr (fiber_affine_exponent32 hN hr0 hrh hw0)
  have hc : 0 ≤ ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
      (fiberAffineG ((M : ℝ) / mu) - fiberSquareOffset q M j) :=
    mul_nonneg (by positivity) (fiber_affine_g_window ht hw)
  exact (add_le_add le_rfl (mul_le_mul_of_nonneg_left he hc)).trans
    (fiber_affine_minorant (by omega) hq0 hqh hrl hmu ht j hw)

end Erdos993Lean.Analytic.V213
