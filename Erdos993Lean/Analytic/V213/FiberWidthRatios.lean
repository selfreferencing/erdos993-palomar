module

public import Erdos993Lean.Analytic.V213.FiberWindowGeometry

/-!
All-real width comparisons used by the Eq74 mass-error ranges.
The printed square-root envelopes are propagated from their starting widths;
all bounds preserve the actual width variable and closed endpoints.
No finite data is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_width_root_ratio_antitone {N M : ℝ} (hN : 1 ≤ N) (hNM : N ≤ M) :
    Real.sqrt M / (M + 1) ≤ Real.sqrt N / (N + 1) := by
  have hN0 : 0 < N := by linarith
  have hM0 : 0 < M := by linarith
  have hx0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg N
  have hy0 : 0 ≤ Real.sqrt M := Real.sqrt_nonneg M
  have hxy : Real.sqrt N ≤ Real.sqrt M := Real.sqrt_le_sqrt hNM
  have hx : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN
  have hy : 1 ≤ Real.sqrt M := hx.trans hxy
  have hsqN : Real.sqrt N ^ 2 = N := Real.sq_sqrt hN0.le
  have hsqM : Real.sqrt M ^ 2 = M := Real.sq_sqrt hM0.le
  have hprod : 1 ≤ Real.sqrt M * Real.sqrt N := by
    have h := mul_le_mul hy hx (by norm_num : (0 : ℝ) ≤ 1) hy0
    simpa using h
  have hp := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hprod)
  apply (div_le_div_iff₀ (by positivity : 0 < M + 1) (by positivity : 0 < N + 1)).2
  have heq : Real.sqrt N * (M + 1) - Real.sqrt M * (N + 1) =
      (Real.sqrt M - Real.sqrt N) * (Real.sqrt M * Real.sqrt N - 1) := by
    generalize hn : Real.sqrt N = x
    generalize hm : Real.sqrt M = y
    have hx' : x ^ 2 = N := by simpa [hn] using hsqN
    have hy' : y ^ 2 = M := by simpa [hm] using hsqM
    rw [← hx', ← hy']
    ring
  linarith

noncomputable def fiberWidthRatio (A c N : ℝ) : ℝ :=
  (A * Real.sqrt N + c) / (N + 1)

theorem fiber_width_ratio_antitone {A c N M : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hN : 1 ≤ N) (hNM : N ≤ M) :
    fiberWidthRatio A c M ≤ fiberWidthRatio A c N := by
  have hroot := mul_le_mul_of_nonneg_left (fiber_width_root_ratio_antitone hN hNM) hA
  have hrecip := mul_le_mul_of_nonneg_left
    (one_div_le_one_div_of_le (by linarith : 0 < N + 1) (by linarith : N + 1 ≤ M + 1)) hc
  unfold fiberWidthRatio
  convert add_le_add hroot hrecip using 1 <;> ring

theorem fiber_window_envelopes {N r W : ℝ}
    (hN : 0 < N) (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (hW : 0 ≤ W) :
    0 ≤ fiberWindowRight N r W ∧
    fiberWindowRight N r W ≤ fiberWidthRatio (Real.sqrt W) 0 N ∧
    0 ≤ fiberWindowLeft N r W ∧
    fiberWindowLeft N r W ≤ fiberWidthRatio (Real.sqrt W) 1 N := by
  have hNa : W * N * (1 - r ^ 2) ≤ W * N := by
    have ha : 1 - r ^ 2 ≤ 1 := by nlinarith [sq_nonneg r]
    simpa using mul_le_mul_of_nonneg_left ha (mul_nonneg hW hN.le)
  have hroot : Real.sqrt (W * N * (1 - r ^ 2)) ≤ Real.sqrt W * Real.sqrt N := by
    rw [← Real.sqrt_mul hW]
    exact Real.sqrt_le_sqrt hNa
  have hrR : 0 ≤ fiberWindowRight N r W := by unfold fiberWindowRight; positivity
  have hrL : 0 ≤ fiberWindowLeft N r W := by
    unfold fiberWindowLeft
    exact add_nonneg hrR (by positivity)
  have hb : fiberWindowRight N r W ≤ fiberWidthRatio (Real.sqrt W) 0 N := by
    unfold fiberWindowRight fiberWidthRatio
    simpa using div_le_div_of_nonneg_right hroot (by positivity : 0 ≤ N + 1)
  refine ⟨hrR, hb, hrL, ?_⟩
  unfold fiberWindowLeft
  calc
    fiberWindowRight N r W + 2 * r / (N + 1) ≤
        fiberWidthRatio (Real.sqrt W) 0 N + 1 / (N + 1) := by
      exact add_le_add hb (div_le_div_of_nonneg_right (by linarith) (by positivity))
    _ = fiberWidthRatio (Real.sqrt W) 1 N := by
      unfold fiberWidthRatio
      ring

end Erdos993Lean.Analytic.V213
