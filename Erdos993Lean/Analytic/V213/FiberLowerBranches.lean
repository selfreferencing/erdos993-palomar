module

public import Erdos993Lean.Analytic.V213.FiberMassConsumers

/-!
All-natural-width elementary branches. The normalized exact
kernel includes M=0 and every integer rank. Its nonnegative lower-offset
term settles the small-t region and the w>=1 region without any positive-
width/rpow assumption. No new finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.NoValley

theorem fiber_square_offset_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (M : ℕ) (j : ℤ) : 0 ≤ fiberSquareOffset q M j := by
  unfold fiberSquareOffset
  exact div_nonneg (sq_nonneg _) (mul_nonneg (fiber_variance_pos hq0 hq1).le (by positivity))

theorem fiber_lower_offset_base {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    (((M : ℝ) + 2) / mu) * fiberSquareOffset q M j ≤ fiberF q mu M j := by
  rw [fiber_F_normalized M j hq0 hq1 hmu]
  have hbin := binom_nonneg hq0.le hq1.le (M := M + 2) (j + 1)
  have hP : 0 ≤ mu ^ (3 / 2 : ℝ) * Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) /
      (2 * fiberAG * ((M : ℝ) + 1)) := by
    have hG := fiber_AG_pos
    positivity
  have hterm := mul_nonneg hP (sub_nonneg.mpr hw)
  linarith

theorem fiber_lower_offset_nonneg {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    0 ≤ fiberF q mu M j := by
  exact (mul_nonneg (by positivity) (fiber_square_offset_nonneg hq0 hq1 M j)).trans
    (fiber_lower_offset_base hq0 hq1 hmu M j hw)

theorem fiber_lower_small_ratio {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 19 ≤ mu) (M : ℕ) (j : ℤ) (hw : fiberSquareOffset q M j ≤ fiberBonus q M)
    (ht : (M : ℝ) / mu ≤ 3 / 5) :
    fiberPsi ((M : ℝ) / mu) + 1 / (4 * mu) ≤ fiberF q mu M j := by
  have hmu0 : 0 < mu := by linarith
  have ht0 : 0 ≤ (M : ℝ) / mu := div_nonneg (Nat.cast_nonneg M) hmu0.le
  have hp : fiberPsi ((M : ℝ) / mu) ≤ -(3 / 25 : ℝ) := by
    unfold fiberPsi
    nlinarith [sq_nonneg ((M : ℝ) / mu - 3 / 5)]
  have hc : 1 / (4 * mu) ≤ (1 / 76 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  exact (by linarith : fiberPsi ((M : ℝ) / mu) + 1 / (4 * mu) ≤ 0).trans
    (fiber_lower_offset_nonneg hq0 hq1 hmu0 M j hw)

theorem fiber_lower_at_least_one {q mu : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hmu : 0 < mu) (M : ℕ) (j : ℤ) (hw : fiberSquareOffset q M j ≤ fiberBonus q M)
    (hw1 : 1 ≤ fiberSquareOffset q M j) :
    fiberPsi ((M : ℝ) / mu) + 1 / (4 * mu) ≤ fiberF q mu M j := by
  have hbase := fiber_lower_offset_base hq0 hq1 hmu M j hw
  have hmul := mul_le_mul_of_nonneg_left hw1 (by positivity : 0 ≤ ((M : ℝ) + 2) / mu)
  have hpsi : fiberPsi ((M : ℝ) / mu) ≤ (M : ℝ) / mu := by
    unfold fiberPsi
    nlinarith [sq_nonneg ((M : ℝ) / mu - 1)]
  have he : ((M : ℝ) + 2) / mu = (M : ℝ) / mu + 2 / mu := by ring
  have hdiv : 1 / (4 * mu) ≤ 2 / mu := by
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * mu) hmu).2
    nlinarith
  rw [mul_one, he] at hmul
  rw [he] at hbase
  linarith

theorem fiber_lower_integer_width {mu : ℝ} {M : ℕ} (hmu : 19 ≤ mu)
    (ht : 3 / 5 ≤ (M : ℝ) / mu) : 12 ≤ M := by
  have hmu0 : 0 < mu := by linarith
  have h := (le_div_iff₀ hmu0).mp ht
  have hM : (11 : ℝ) < M := by linarith
  have hnat : 11 < M := by exact_mod_cast hM
  omega

end Erdos993Lean.Analytic.V213
