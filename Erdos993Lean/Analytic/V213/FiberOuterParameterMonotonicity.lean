module

public import Erdos993Lean.Analytic.V213.FiberOuterGainBounds

/-!
Actual outer parameter comparisons in N and y. Every real N>=17
and all closed skew endpoints are retained. The resulting envelope
comparison in N follows directly from the actual clipped G monotonicity,
not from a sampled endpoint or an assumed extension theorem.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_outer_R_increases_N {y : ℝ} (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) :
    MonotoneOn (fun N => fiberOuterR N y) (Ici (17 : ℝ)) := by
  intro N hN M hM hNM
  change 17 ≤ N at hN
  change 17 ≤ M at hM
  have hn : 0 < N + 1 := by linarith only [hN]
  have hm : 0 < M + 1 := by linarith only [hM]
  have hy : 0 < 1 - y := by linarith only [hyh]
  have hcn := fiber_outer_chi_pos hN
  have hcm := fiber_outer_chi_pos hM
  have hc := fiber_outer_chi_increases hN hM hNM
  have hrho : N / (N + 1) ≤ M / (M + 1) := by
    apply (div_le_div_iff₀ hn hm).2
    nlinarith only [hNM]
  have hbase := mul_le_mul_of_nonneg_left hrho hy.le
  have h2 : 2 / (M + 1) ≤ 2 / (N + 1) :=
    div_le_div_of_nonneg_left (by norm_num) hn (by linarith only [hNM])
  have hnum : 2 / (M + 1) + y / (3 * (1 - y)) ≤
      2 / (N + 1) + y / (3 * (1 - y)) := by linarith only [h2]
  have hnum0 : 0 ≤ 2 / (N + 1) + y / (3 * (1 - y)) := by positivity
  have hloss := (div_le_div_of_nonneg_right hnum hcm.le).trans
    (div_le_div_of_nonneg_left hnum0 hcn hc)
  unfold fiberOuterR
  simp only [mul_div_assoc]
  linarith only [hbase,hloss]

theorem fiber_outer_Delta_increases_y {N : ℝ} (hN : 17 ≤ N) :
    StrictMonoOn (fiberOuterDelta N) (Icc 0 (4 / 25 : ℝ)) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberOuterDeltaPrime N) (convex_Icc _ _)
  · intro y hy
    exact (fiber_hasDerivAt_outer_Delta (N := N) (by linarith only [hy.2])).continuousAt.continuousWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    exact (fiber_hasDerivAt_outer_Delta (N := N) (by linarith only [hy'.2])).hasDerivWithinAt
  · intro y hy
    have hy' : y ∈ Icc 0 (4 / 25 : ℝ) := interior_subset hy
    exact fiber_outer_DeltaPrime_positive hN (by linarith only [hy'.2])

theorem fiber_outer_Delta_increases_N {y : ℝ} (hy0 : 0 < y) (hyh : y < 1) :
    StrictMonoOn (fun N => fiberOuterDelta N y) (Ici (17 : ℝ)) := by
  intro N hN M hM hNM
  change 17 ≤ N at hN
  change 17 ≤ M at hM
  have hn : 0 < N := by linarith only [hN]
  have hm : 0 < M := by linarith only [hM]
  have hprod : 1 < N * M := by nlinarith only [hN,hM]
  have hinv : 1 / (N * M) < 1 := (div_lt_one (mul_pos hn hm)).2 hprod
  have he : (M - 1 + 1 / M) - (N - 1 + 1 / N) = (M - N) * (1 - 1 / (N * M)) := by
    field_simp [hn.ne',hm.ne']
    ring
  have hh : N - 1 + 1 / N < M - 1 + 1 / M := by
    have hp := mul_pos (sub_pos.mpr hNM) (sub_pos.mpr hinv)
    linarith only [he,hp]
  unfold fiberOuterDelta
  exact mul_lt_mul_of_pos_left hh (div_pos hy0 (by linarith only [hyh]))

theorem fiber_outer_U_increases_N {a n : ℝ} (ha : 0 < a) (hah : a ≤ 2 / 5)
    (hn : 17 ≤ n) (hna : 18 / 5 ≤ (n + 1) * a) (t : ℝ) :
    StrictMonoOn (fun N => fiberOuterU N (a ^ 2) t) (Ici n) := by
  intro N hN M hM hNM
  change n ≤ N at hN
  change n ≤ M at hM
  have hnN : 17 ≤ N := hn.trans hN
  have hnM : 17 ≤ M := hn.trans hM
  have hy0 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hyh : a ^ 2 ≤ (4 / 25 : ℝ) := by nlinarith only [ha,hah]
  have hrN := fiber_outer_R_pos hnN hy0.le hyh
  have hrM := fiber_outer_R_pos hnM hy0.le hyh
  have hR := fiber_outer_R_increases_N hy0.le hyh hnN hnM hNM.le
  have hP := (fiber_outer_P_increases_N ha hah hn hna) hN hM hNM
  have hD := (fiber_outer_Delta_increases_N hy0 (by linarith only [hyh])) hnN hnM hNM
  dsimp at hP hD hR
  have harg : (5 / 2 : ℝ) * Real.log t + fiberOuterP N (a ^ 2) ≤
      (5 / 2 : ℝ) * Real.log t + fiberOuterP M (a ^ 2) := by linarith only [hP]
  have hG := shared_G_antitoneOn_nonpos (min_le_left (0 : ℝ) _) (min_le_left (0 : ℝ) _)
    (min_le_min_left (0 : ℝ) harg)
  have hcoef := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by linarith only [hrN]) hR
  have hloss := mul_le_mul hG hcoef (by positivity : 0 ≤ 2 / fiberOuterR M (a ^ 2))
    (shared_G_nonneg (min 0 ((5 / 2 : ℝ) * Real.log t + fiberOuterP N (a ^ 2))))
  unfold fiberOuterU
  linarith only [hD,hloss]

end Erdos993Lean.Analytic.V213
