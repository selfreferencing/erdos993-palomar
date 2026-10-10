module

public import Erdos993Lean.Analytic.V213.FiberDefinitions
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Convex.Deriv

/-!
Supported-index and whole-width geometry for the actual mass window.
All widths and offsets are real in the
analytic lemmas; the integer-rank consumer uses the actual printed offset.
No finite family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberWindowRight (N r W : ℝ) : ℝ :=
  Real.sqrt (W * N * (1 - r ^ 2)) / (N + 1)

noncomputable def fiberWindowLeft (N r W : ℝ) : ℝ :=
  fiberWindowRight N r W + 2 * r / (N + 1)

noncomputable def fiberMassError (N r W : ℝ) : ℝ :=
  (N + 1) / (12 * (1 - r ^ 2)) *
    max ((fiberWindowLeft N r W) ^ 4 / (1 - (fiberWindowLeft N r W) ^ 2))
      ((fiberWindowRight N r W) ^ 4 / (1 - (r + fiberWindowRight N r W) ^ 2))

theorem fiber_supported_window_real {N r W u J : ℝ}
    (hN : 14 ≤ N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2)
    (hW0 : 0 ≤ W) (hWh : W ≤ 3 / 2)
    (hu : u ^ 2 ≤ W * N * (1 - r ^ 2) / 4)
    (hJ : J = N / 2 + r * (N - 1) / 2 + u) :
    0 < J ∧ J < N := by
  have hN0 : 0 < N := by linarith
  have ha0 : 0 ≤ 1 - r ^ 2 := by nlinarith
  have ha1 : 1 - r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
  have hu' : u ^ 2 ≤ 3 * N / 8 := by
    have ha := mul_le_mul_of_nonneg_left ha1 (mul_nonneg hW0 hN0.le)
    have hw := mul_le_mul_of_nonneg_right hWh hN0.le
    nlinarith
  have hL : (N / 2) ^ 2 > 3 * N / 8 := by nlinarith [sq_nonneg (N - 14)]
  have hR : ((N + 1) / 4) ^ 2 > 3 * N / 8 := by nlinarith [sq_nonneg (N - 14)]
  have huL : -N / 2 < u := by
    by_contra h
    have ht : u ≤ -N / 2 := le_of_not_gt h
    have hp := mul_nonneg (by linarith : 0 ≤ -u - N / 2)
      (by linarith : 0 ≤ -u + N / 2)
    nlinarith
  have huR : u < (N + 1) / 4 := by
    by_contra h
    have ht : (N + 1) / 4 ≤ u := le_of_not_gt h
    have hp := mul_nonneg (by linarith : 0 ≤ u - (N + 1) / 4)
      (by linarith : 0 ≤ u + (N + 1) / 4)
    nlinarith
  have hprod0 : 0 ≤ r * (N - 1) := mul_nonneg hr0 (by linarith)
  have hprodh : r * (N - 1) ≤ (N - 1) / 2 := by
    have h := mul_le_mul_of_nonneg_right hrh (by linarith : 0 ≤ N - 1)
    linarith
  constructor <;> linarith

theorem fiber_supported_window {M : ℕ} {q W : ℝ} (hM : 12 ≤ M)
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4)
    (hW0 : 0 ≤ W) (hWh : W ≤ 3 / 2) (j : ℤ)
    (hu : fiberOffset q M j ^ 2 ≤ W * ((M : ℝ) + 2) *
      (1 - fiberSkew q ^ 2) / 4) :
    0 ≤ j + 1 ∧ j + 1 ≤ ((M + 2 : ℕ) : ℤ) := by
  have hN : (14 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 14 ≤ M + 2)
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hJ : (j : ℝ) + 1 = ((M : ℝ) + 2) / 2 +
      fiberSkew q * (((M : ℝ) + 2) - 1) / 2 + fiberOffset q M j := by
    unfold fiberOffset fiberSkew
    ring
  have h := fiber_supported_window_real hN hr0 hrh hW0 hWh hu hJ
  constructor
  · exact_mod_cast h.1.le
  · have hh : (j : ℝ) + 1 ≤ ((M + 2 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat] using h.2.le
    exact_mod_cast hh

noncomputable def fiberWidthPower (A c N : ℝ) : ℝ :=
  (A * Real.sqrt N + c) ^ 4 / (N + 1) ^ 3

theorem fiber_width_power_deriv {A c N : ℝ} (hN : 0 < N) :
    HasDerivAt (fiberWidthPower A c)
      ((A * Real.sqrt N + c) ^ 3 / (N + 1) ^ 4 *
        (A * (2 - N) / Real.sqrt N - 3 * c)) N := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hn1 : N + 1 ≠ 0 := by positivity
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN.le
  convert ((((Real.hasDerivAt_sqrt hN.ne').const_mul A).add_const c).pow 4).div
    (((hasDerivAt_id N).add_const 1).pow 3) (pow_ne_zero 3 hn1) using 1
  · funext x
    rfl
  · dsimp
    field_simp [hs.ne', hn1]
    generalize he : Real.sqrt N = s
    have hh : s ^ 2 = N := by simpa [he] using hsq
    rw [← hh]
    ring

theorem fiber_width_power_antitone {A c : ℝ} (hA : 0 ≤ A) (hc : 0 ≤ c) :
    AntitoneOn (fiberWidthPower A c) (Ici 2) := by
  have hd : ∀ N ∈ Ici (2 : ℝ), HasDerivAt (fiberWidthPower A c)
      ((A * Real.sqrt N + c) ^ 3 / (N + 1) ^ 4 *
        (A * (2 - N) / Real.sqrt N - 3 * c)) N := by
    intro N hN
    have hN2 : 2 ≤ N := hN
    exact fiber_width_power_deriv (by linarith)
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 2)
    (fun N hN => (hd N hN).continuousAt.continuousWithinAt)
    (fun N hN => (hd N (interior_subset hN)).hasDerivWithinAt)
  intro N hN
  have hN' : N ∈ Ici (2 : ℝ) := interior_subset hN
  have hN2 : 2 ≤ N := hN'
  apply mul_nonpos_of_nonneg_of_nonpos (by positivity)
  apply sub_nonpos.mpr
  have ht : A * (2 - N) / Real.sqrt N ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hA (by linarith))
      (Real.sqrt_nonneg N)
  linarith

end Erdos993Lean.Analytic.V213
