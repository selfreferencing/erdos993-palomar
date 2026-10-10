module

public import Erdos993Lean.Analytic.V213.FiberWindowAnchor

/-!
Eq102: the inverse input controls the actual clipped G loss in both
signs of omega. The comparison uses the decreasing function (1-u)^2/u
on its full domain (0,1], and a positive actual rate.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

theorem fiber_window_penalty_antitone {w u : ℝ} (hw : 0 < w) (hwu : w ≤ u)
    (hu : u ≤ 1) : (1 - u) ^ 2 / u ≤ (1 - w) ^ 2 / w := by
  have hu0 : 0 < u := hw.trans_le hwu
  have hw1 : w ≤ 1 := hwu.trans hu
  have hprod : u * w ≤ 1 := by nlinarith only [hw.le,hu,hw1,hu0.le]
  apply (div_le_div_iff₀ hu0 hw).2
  have h := mul_nonneg (sub_nonneg.mpr hwu) (sub_nonneg.mpr hprod)
  nlinarith only [h]

theorem fiber_window_G_loss {w omega : ℝ} (hw : 0 < w)
    (hwu : w ≤ 1 + V22.rootMap omega) (homega : omega ≤ 0) :
    V22.G omega ≤ (1 - w) ^ 2 / w := by
  have hs := shared_rootMap_monotone homega
  rw [shared_rootMap_zero] at hs
  have hu : 1 + V22.rootMap omega ≤ 1 := by linarith only [hs]
  have h := fiber_window_penalty_antitone hw hwu hu
  unfold V22.G
  convert h using 1 <;> ring

theorem fiber_window_clipped_loss {l v gain omega rho rho0 : ℝ}
    (hl : 0 < l) (hv : 0 < v) (hg : 0 ≤ 1 + gain)
    (homega : (5 / 2) * Real.log l + gain ≤ omega)
    (hrho0 : 0 < rho0) (hrho : rho0 ≤ rho) :
    2 / rho * V22.G (min 0 omega) ≤
      2 * (1 - fiberWindowInverse (fiberWindowAnchor l v gain)) ^ 2 /
        (rho0 * fiberWindowInverse (fiberWindowAnchor l v gain)) := by
  let w := fiberWindowInverse (fiberWindowAnchor l v gain)
  have hx := fiber_window_anchor_domain hl hv hg
  have hw : 0 < w := fiber_window_inverse_positive hx.1
  have hp : 0 ≤ (1 - w) ^ 2 / w := by positivity
  have hR : 0 < rho := hrho0.trans_le hrho
  have hG : V22.G (min 0 omega) ≤ (1 - w) ^ 2 / w := by
    by_cases ho : omega ≤ 0
    · rw [min_eq_right ho]
      exact fiber_window_G_loss hw (fiber_window_anchor_root hl hv hg homega) ho
    · rw [min_eq_left (le_of_not_ge ho),shared_G_zero]
      exact hp
  have hrec : 2 / rho ≤ 2 / rho0 := div_le_div_of_nonneg_left (by norm_num) hrho0 hrho
  have hG0 : 0 ≤ V22.G (min 0 omega) := shared_G_nonneg _
  have hmul := mul_le_mul hrec hG hG0 (by positivity : 0 ≤ 2 / rho0)
  have he : (2 / rho0) * ((1 - w) ^ 2 / w) = 2 * (1 - w) ^ 2 / (rho0 * w) := by
    rw [div_mul_div_comm]
  simpa only [he] using hmul

end Erdos993Lean.Analytic.V213
