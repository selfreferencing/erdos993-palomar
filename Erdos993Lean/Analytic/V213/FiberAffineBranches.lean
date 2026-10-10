module

public import Erdos993Lean.Analytic.V213.FiberLowerBranches

/-!
The first two tests of Theorem6.15: exact Eq84 completed-square margin on
w>=3/2, and the small-ratio branch including M=0. The actual nonnegative
kernel range supplies F>=Bw. All b/beta endpoints and natural widths are
retained; no finite checker or later curvature premise is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_affine_completed_square (t b beta : ℝ) :
    (3 / 2 : ℝ) * t - fiberPsi t - b - beta * (t - 1) =
      9 / 2 * (t - (17 + 2 * beta) / 18) ^ 2 +
        (35 / 4 + beta - beta ^ 2 - 18 * b) / 18 := by
  unfold fiberPsi
  ring

theorem fiber_affine_three_half_margin {t b beta : ℝ}
    (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1) :
    fiberPsi t + b + beta * (t - 1) + 31 / 360 ≤ (3 / 2 : ℝ) * t := by
  have hp : 0 ≤ beta * (1 - beta) := mul_nonneg hbeta0 (by linarith only [hbetah])
  have hs := sq_nonneg (t - (17 + 2 * beta) / 18)
  have he := fiber_affine_completed_square t b beta
  nlinarith only [hp,hs,he,hb]

theorem fiber_affine_large_offset {q mu b beta : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (hbetah : beta ≤ 1)
    (M : ℕ) (j : ℤ) (hwl : 3 / 2 ≤ fiberSquareOffset q M j)
    (hwh : fiberSquareOffset q M j ≤ fiberBonus q M) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤
      fiberF q mu M j := by
  have ht : 0 ≤ (M : ℝ) / mu := by positivity
  have hw0 : 0 ≤ fiberSquareOffset q M j := by linarith only [hwl]
  have hm := fiber_lower_offset_base hq0 hq1 hmu M j hwh
  have hrate : (M : ℝ) / mu ≤ ((M : ℝ) + 2) / mu :=
    div_le_div_of_nonneg_right (by linarith) hmu.le
  have htw := mul_le_mul_of_nonneg_right hrate hw0
  have hwl' := mul_le_mul_of_nonneg_left hwl ht
  have hmargin := fiber_affine_three_half_margin (t := (M : ℝ) / mu) hb hbeta0 hbetah
  nlinarith only [hm,htw,hwl',hmargin]

theorem fiber_affine_small_target {t b beta : ℝ} (ht0 : 0 ≤ t) (hth : t ≤ 1 / 2)
    (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) :
    fiberPsi t + b + beta * (t - 1) ≤ -(9 / 40 : ℝ) := by
  have hp : beta * (t - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hbeta0 (by linarith only [hth])
  unfold fiberPsi
  nlinarith only [sq_nonneg (t - 1 / 2),ht0,hth,hb,hp]

theorem fiber_affine_small_ratio {q mu b beta : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (hmu : 0 < mu)
    (hb : b ≤ 2 / 5) (hbeta0 : 0 ≤ beta) (M : ℕ) (j : ℤ)
    (ht : (M : ℝ) / mu ≤ 1 / 2)
    (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    fiberPsi ((M : ℝ) / mu) + b + beta * ((M : ℝ) / mu - 1) + 1 / 28 ≤
      fiberF q mu M j := by
  have htarget := fiber_affine_small_target (by positivity : 0 ≤ (M : ℝ) / mu) ht hb hbeta0
  have hF := fiber_lower_offset_nonneg hq0 hq1 hmu M j hw
  linarith only [htarget,hF]

theorem fiber_affine_width22 {mu : ℝ} (hmu : 40 ≤ mu) {M : ℕ}
    (ht : 1 / 2 ≤ (M : ℝ) / mu) : 20 ≤ M := by
  have hm : 0 < mu := by linarith only [hmu]
  have h := (le_div_iff₀ hm).mp ht
  have hh : (20 : ℝ) ≤ (M : ℝ) := by linarith only [h,hmu]
  exact_mod_cast hh

theorem fiber_affine_width32 {mu : ℝ} (hmu : 40 ≤ mu) {M : ℕ}
    (ht : 3 / 4 ≤ (M : ℝ) / mu) : 30 ≤ M := by
  have hm : 0 < mu := by linarith only [hmu]
  have h := (le_div_iff₀ hm).mp ht
  have hh : (30 : ℝ) ≤ (M : ℝ) := by linarith only [h,hmu]
  exact_mod_cast hh

end Erdos993Lean.Analytic.V213
