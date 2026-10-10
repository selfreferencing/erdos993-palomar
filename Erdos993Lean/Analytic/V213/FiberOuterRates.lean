module

public import Erdos993Lean.Analytic.V213.FiberOuterDefinitions

/-!
Printed closed-domain outer-rate controls.
The displayed rational lower bound and derivative cap are proved for
all real N>=17 and y in[0,4/25], not merely sampled start rows.
All denominator signs follow from the proved chi bound.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberOuterRPrime (N y : ℝ) : ℝ :=
  -N / (N + 1) - 1 / (3 * fiberOuterChi N * (1 - y) ^ 2)

noncomputable def fiberOuterDeltaPrime (N y : ℝ) : ℝ :=
  (N - 1 + 1 / N) / (1 - y) ^ 2

theorem fiber_outer_R_lower {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    59869 / 97650 ≤ fiberOuterR N y := by
  have hn : 0 < N := by linarith only [hN]
  have hm : 0 < N + 1 := by linarith only [hN]
  have hy : 0 < 1 - y := by linarith only [hyh]
  have hc := fiber_outer_chi_pos hN
  have hY : (21 / 25 : ℝ) ≤ 1 - y := by linarith only [hyh]
  have hRho : (17 / 18 : ℝ) ≤ N / (N + 1) := by
    apply (le_div_iff₀ hm).2
    linarith only [hN]
  have hbase := mul_le_mul hY hRho (by norm_num : (0 : ℝ) ≤ 17 / 18) hy.le
  have h2 : 2 / (N + 1) ≤ (1 / 9 : ℝ) := by
    apply (div_le_iff₀ hm).2
    linarith only [hN]
  have hfrac : y / (3 * (1 - y)) ≤ (4 / 63 : ℝ) := by
    apply (div_le_iff₀ (by positivity : 0 < 3 * (1 - y))).2
    linarith only [hyh]
  have hnum : 2 / (N + 1) + y / (3 * (1 - y)) ≤ (1 / 9 + 4 / 63 : ℝ) := by
    linarith only [h2,hfrac]
  have hdiv := (div_le_div_of_nonneg_right hnum hc.le).trans
    (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1 / 9 + 4 / 63)
      (by norm_num : (0 : ℝ) < 31 / 32) (fiber_outer_chi_bounds hN).1)
  unfold fiberOuterR
  have he : (1 - y) * N / (N + 1) = (1 - y) * (N / (N + 1)) := by ring
  rw [he]
  linarith only [hbase,hdiv]

theorem fiber_outer_R_pos {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    3 / 5 < fiberOuterR N y := by
  linarith only [fiber_outer_R_lower hN hy0 hyh]

theorem fiber_hasDerivAt_outer_R {N y : ℝ} (hN : 17 ≤ N) (hy : y < 1) :
    HasDerivAt (fiberOuterR N) (fiberOuterRPrime N y) y := by
  have hchi := fiber_outer_chi_pos hN
  have hden : 0 < 1 - y := by linarith only [hy]
  have h1 := ((hasDerivAt_id y).const_sub 1).const_mul (N / (N + 1))
  have h2 := (hasDerivAt_id y).div (((hasDerivAt_id y).const_sub 1).const_mul 3) (by positivity)
  have h := h1.sub ((h2.const_add (2 / (N + 1))).div_const (fiberOuterChi N))
  convert h using 1
  · funext x
    dsimp [fiberOuterR]
    ring
  · dsimp [fiberOuterRPrime]
    field_simp [hchi.ne',hden.ne']
    ring

theorem fiber_outer_RPrime_negative {N y : ℝ} (hN : 17 ≤ N) (hy : y < 1) :
    fiberOuterRPrime N y < 0 := by
  have hn : 0 < N := by linarith only [hN]
  have hm : 0 < N + 1 := by linarith only [hN]
  have hc := fiber_outer_chi_pos hN
  have hy : 0 < 1 - y := by linarith only [hy]
  unfold fiberOuterRPrime
  simp only [neg_div]
  have h1 : 0 < N / (N + 1) := by positivity
  have h2 : 0 < 1 / (3 * fiberOuterChi N * (1 - y) ^ 2) := by positivity
  linarith only [h1,h2]

theorem fiber_outer_RPrime_bound {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    -fiberOuterRPrime N y ≤ 61013 / 41013 := by
  have hn : 0 < N := by linarith only [hN]
  have hm : 0 < N + 1 := by linarith only [hN]
  have hc := fiber_outer_chi_pos hN
  have hy : 0 < 1 - y := by linarith only [hyh]
  have hY : (21 / 25 : ℝ) ≤ 1 - y := by linarith only [hyh]
  have hsq := (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 21 / 25) hy.le).2 hY
  have hp := mul_le_mul (fiber_outer_chi_bounds hN).1 hsq (by norm_num : (0 : ℝ) ≤ (21 / 25) ^ 2) hc.le
  have hden : 3 * (31 / 32 : ℝ) * (21 / 25) ^ 2 ≤ 3 * fiberOuterChi N * (1 - y) ^ 2 := by
    nlinarith only [hp]
  have hdiv := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1)
    (by norm_num : (0 : ℝ) < 3 * (31 / 32) * (21 / 25) ^ 2) hden
  conv at hdiv => rhs; norm_num
  have hr : N / (N + 1) ≤ 1 := (div_le_one hm).2 (by linarith)
  unfold fiberOuterRPrime
  simp only [neg_div]
  linarith only [hdiv,hr]

theorem fiber_outer_rate_slope_ratio {N y : ℝ} (hN : 17 ≤ N) (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    -fiberOuterRPrime N y / fiberOuterR N y < 5 / 2 := by
  have hr := fiber_outer_R_pos hN hy0 hyh
  have hs := fiber_outer_RPrime_bound hN hy0 hyh
  apply (div_lt_iff₀ (by linarith only [hr] : 0 < fiberOuterR N y)).2
  linarith only [hr,hs]

theorem fiber_hasDerivAt_outer_Delta {N y : ℝ} (hy : y < 1) :
    HasDerivAt (fiberOuterDelta N) (fiberOuterDeltaPrime N y) y := by
  have hden : 0 < 1 - y := by linarith only [hy]
  have h := ((hasDerivAt_id y).div ((hasDerivAt_id y).const_sub 1) hden.ne').const_mul (N - 1 + 1 / N)
  convert h using 1
  · funext x
    dsimp [fiberOuterDelta]
    ring
  · dsimp [fiberOuterDeltaPrime]
    field_simp [hden.ne']
    ring

theorem fiber_outer_DeltaPrime_positive {N y : ℝ} (hN : 17 ≤ N) (hy : y < 1) :
    0 < fiberOuterDeltaPrime N y := by
  have hn : 0 < N := by linarith only [hN]
  have hy : 0 < 1 - y := by linarith only [hy]
  have hnum : 0 < N - 1 + 1 / N := by
    have hi : 0 < 1 / N := by positivity
    linarith only [hN,hi]
  unfold fiberOuterDeltaPrime
  positivity

end Erdos993Lean.Analytic.V213
