module

public import Erdos993Lean.Analytic.V213.FiberMassCases
public import Erdos993Lean.Analytic.V213.FiberBinomial
public import Erdos993Lean.Analytic.V22.Analysis.GaussianComparison
public import Erdos993Lean.Analytic.V22.Analysis.GaussianExponents

/-!
Exact mass-window definition bridges and analytic domains for Eq73.
The accepted standardized-coordinate definitions are identified with the
actual current square-root windows and E_W. General conditional consumers
retain the printed denominators; the used whole-width ranges discharge them.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_window_right_identity {N r W : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W) :
    Erdos993Lean.Analytic.V22.ZR r N W = fiberWindowRight N r W := by
  have ha := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  have hs := shared_sN_sq hr0 hr1 hN
  have hprod : (2 * Real.sqrt W * Erdos993Lean.Analytic.V22.sN r N) ^ 2 =
      W * N * (1 - r ^ 2) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hW, hs]
    unfold Erdos993Lean.Analytic.V22.varianceR
    ring
  have hroot := Real.sq_sqrt (mul_nonneg (mul_nonneg hW hN.le) ha.le)
  have heq : 2 * Real.sqrt W * Erdos993Lean.Analytic.V22.sN r N =
      Real.sqrt (W * N * (1 - r ^ 2)) := by
    have hp : 0 ≤ 2 * Real.sqrt W * Erdos993Lean.Analytic.V22.sN r N := by
      unfold Erdos993Lean.Analytic.V22.sN
      positivity
    have ht := Real.sqrt_nonneg (W * N * (1 - r ^ 2))
    nlinarith
  unfold Erdos993Lean.Analytic.V22.ZR fiberWindowRight
  rw [heq]

theorem fiber_window_left_identity {N r W : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W) :
    Erdos993Lean.Analytic.V22.ZL r N W = fiberWindowLeft N r W := by
  have heq : Erdos993Lean.Analytic.V22.ZL r N W =
      Erdos993Lean.Analytic.V22.ZR r N W + 2 * r / (N + 1) := by
    unfold Erdos993Lean.Analytic.V22.ZL Erdos993Lean.Analytic.V22.ZR
    ring
  rw [heq, fiber_window_right_identity hN hr0 hr1 hW]
  rfl

theorem fiber_mass_error_identity {N r W : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hr1 : r < 1) (hW : 0 ≤ W) :
    Erdos993Lean.Analytic.V22.quarticError r N W = fiberMassError N r W := by
  have ha := shared_one_sub_sq_pos (by linarith : -1 < r) hr1
  unfold Erdos993Lean.Analytic.V22.quarticError fiberMassError
  rw [fiber_window_left_identity hN hr0 hr1 hW, fiber_window_right_identity hN hr0 hr1 hW]
  rw [mul_max_of_nonneg _ _ (by positivity)]
  congr 1 <;> simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

theorem fiber_mass_window_common {N r W : ℝ}
    (hN : 14 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hW : 1 ≤ W) (hWh : W ≤ 3 / 2) :
    0 < fiberWindowLeft N r W ∧ fiberWindowLeft N r W < 1 ∧
    0 < fiberWindowRight N r W ∧ r + fiberWindowRight N r W < 1 ∧
    (11 / 36 : ℝ) ≤ 1 - (r + fiberWindowRight N r W) ^ 2 ∧
    W * (1 - r ^ 2) * (N / (N + 1)) ≤
      12 * (1 - (r + fiberWindowRight N r W) ^ 2) := by
  have hN0 : 0 < N := by linarith
  have hW0 : 0 < W := by linarith
  have ha0 : 0 < 1 - r ^ 2 := by nlinarith
  have ha1 : 1 - r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hm : 0 < N + 1 := by positivity
  have hroot0 : 0 < Real.sqrt (W * N * (1 - r ^ 2)) := by positivity
  have hR0 : 0 < fiberWindowRight N r W := by unfold fiberWindowRight; positivity
  have hsq := Real.sq_sqrt (mul_pos (mul_pos hW0 hN0) ha0).le
  have hnum : W * N * (1 - r ^ 2) ≤ (3 / 2 : ℝ) * N := by
    have hh := mul_le_mul_of_nonneg_left ha1 (mul_nonneg hW0.le hN0.le)
    have hw := mul_le_mul_of_nonneg_right hWh hN0.le
    nlinarith
  have hroot : 3 * Real.sqrt (W * N * (1 - r ^ 2)) ≤ N + 1 := by
    have hh := mul_nonneg (by linarith : 0 ≤ N - 14) hN0.le
    nlinarith
  have hR : fiberWindowRight N r W ≤ 1 / 3 := by
    unfold fiberWindowRight
    apply (div_le_iff₀ hm).2
    linarith
  have hrec : 1 / (N + 1) ≤ 1 / 15 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hL : fiberWindowLeft N r W ≤ 2 / 5 := by
    unfold fiberWindowLeft
    have hh := div_le_div_of_nonneg_right (by linarith : 2 * r ≤ 1) hm.le
    linarith
  have hL0 : 0 < fiberWindowLeft N r W := by
    unfold fiberWindowLeft
    exact add_pos_of_pos_of_nonneg hR0 (by positivity)
  have hsum0 : 0 ≤ r + fiberWindowRight N r W := by positivity
  have hsum : r + fiberWindowRight N r W ≤ 5 / 6 := by linarith
  have hD : (11 / 36 : ℝ) ≤ 1 - (r + fiberWindowRight N r W) ^ 2 := by nlinarith
  have hrho : 0 ≤ N / (N + 1) := by positivity
  have hrho1 : N / (N + 1) ≤ 1 := (div_le_one hm).2 (by linarith)
  have hprod : W * (1 - r ^ 2) * (N / (N + 1)) ≤ 3 / 2 := by
    have hw := mul_le_mul_of_nonneg_left ha1 hW0.le
    have hh := mul_le_mul_of_nonneg_left hrho1 (mul_nonneg hW0.le ha0.le)
    nlinarith
  exact ⟨hL0, by linarith, hR0, by linarith, hD, by linarith⟩

end Erdos993Lean.Analytic.V213
