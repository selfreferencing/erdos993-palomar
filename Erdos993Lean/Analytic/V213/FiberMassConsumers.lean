module

public import Erdos993Lean.Analytic.V213.FiberLowerNormalized

/-!
Concrete mass-window consumers. Every support/denominator/absorption
guard of the general Eq73 theorem is proved on the full used window range,
including both closed skew endpoints and all natural widths. No finite data
or Section 5 statement is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_mass_used_window_guards {M : ℕ} (hM : 12 ≤ M) {q W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hW : 1 ≤ W) (hWh : W ≤ 3 / 2)
    (j : ℤ) (hw : fiberSquareOffset q M j ≤ W) :
    (0 ≤ j + 1 ∧ j + 1 ≤ ((M + 2 : ℕ) : ℤ)) ∧
    0 < 1 - (fiberWindowLeft ((M : ℝ) + 2) (fiberSkew q) W) ^ 2 ∧
    0 < 1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2 ∧
    W ≤ 12 * (1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2) /
      ((1 - fiberSkew q ^ 2) * Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2)) := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hv := fiber_variance_pos hq0' hq1
  have hN : (14 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 14 ≤ M + 2)
  have hN0 : 0 < (M : ℝ) + 2 := by positivity
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hW0 : 0 ≤ W := by linarith
  have hu : fiberOffset q M j ^ 2 ≤ W * ((M : ℝ) + 2) * (1 - fiberSkew q ^ 2) / 4 := by
    unfold fiberSquareOffset at hw
    have hh := (div_le_iff₀ (mul_pos hv hN0)).mp hw
    rw [fiber_variance_skew]
    convert hh using 1 <;> ring
  have hJ := fiber_supported_window hM hq0 hqh hW0 hWh j hu
  have hc := fiber_mass_window_common hN hr0 hrh hW hWh
  have hL : 0 < 1 - (fiberWindowLeft ((M : ℝ) + 2) (fiberSkew q) W) ^ 2 := by
    nlinarith [hc.1, hc.2.1]
  have hR : 0 < 1 - (fiberSkew q + fiberWindowRight ((M : ℝ) + 2) (fiberSkew q) W) ^ 2 := by
    linarith [hc.2.2.2.2.1]
  have ha : 0 < 1 - fiberSkew q ^ 2 := by rw [fiber_variance_skew]; positivity
  have hrho : 0 < Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) := by
    unfold Erdos993Lean.Analytic.V22.rho
    positivity
  refine ⟨hJ, hL, hR, ?_⟩
  apply (le_div_iff₀ (mul_pos ha hrho)).2
  unfold Erdos993Lean.Analytic.V22.rho
  simpa only [mul_assoc] using hc.2.2.2.2.2

theorem fiber_binomial_mass_lower_used_windows {M : ℕ} (hM : 12 ≤ M) {q W : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hW : 1 ≤ W) (hWh : W ≤ 3 / 2)
    (j : ℤ) (hw : fiberSquareOffset q M j ≤ W) :
    Real.exp (-Erdos993Lean.Analytic.V22.rho ((M : ℝ) + 2) * fiberSquareOffset q M j / 2 -
      (2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) *
        Real.sqrt (((M : ℝ) + 2) * fiberSquareOffset q M j) +
        2 * (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)) ^ 2) / ((M : ℝ) + 3) -
      fiberMassError ((M : ℝ) + 2) (fiberSkew q) W) ≤
    Real.sqrt (1 - fiberSkew q ^ 2) * binom (M + 2) q (j + 1) /
      fiberCentralPrefactor (M + 2) := by
  have hg := fiber_mass_used_window_guards hM hq0 hqh hW hWh j hw
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hm := fiber_binomial_mass_lower_general (by omega : 2 ≤ M + 2) hr0 hrh hW
    (j + 1) hg.1.1 hg.1.2 (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hg.2.1)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hg.2.2.1)
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hg.2.2.2)
    (by push_cast; rw [fiber_radial_fiber_square]; exact hw)
  push_cast at hm
  rw [fiber_radial_fiber_square, show (1 + fiberSkew q) / 2 = q by unfold fiberSkew; ring] at hm
  simpa only [Nat.cast_add, Nat.cast_ofNat, show ((M : ℝ) + 2) + 1 = (M : ℝ) + 3 by ring] using hm

end Erdos993Lean.Analytic.V213
