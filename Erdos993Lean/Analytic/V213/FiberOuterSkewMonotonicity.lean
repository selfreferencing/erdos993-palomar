module

public import Erdos993Lean.Analytic.V213.FiberOuterParameterMonotonicity

/-!
Whole closed skew-domain monotonicity of the actual outer envelope.
The smooth negative-argument expression has the printed derivative.
At its zero join that derivative is exactly Delta'; comparisons across
the join use the nonnegative G term and do not assume differentiability
of min. No start-row or generated finite family is used.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberOuterRawU (N t y : ℝ) : ℝ :=
  1 + fiberOuterDelta N y - 2 / fiberOuterR N y *
    V22.G ((5 / 2 : ℝ) * Real.log t + fiberOuterP N y)

noncomputable def fiberOuterRawUPrime (N t y : ℝ) : ℝ :=
  fiberOuterDeltaPrime N y +
    (-2 * V22.G1 ((5 / 2 : ℝ) * Real.log t + fiberOuterP N y) / fiberOuterR N y) *
      (fiberOuterPPrimeM (N + 1) y -
        V22.rootMap ((5 / 2 : ℝ) * Real.log t + fiberOuterP N y) *
          fiberOuterRPrime N y / fiberOuterR N y)

theorem fiber_outer_G_root_identity (lambda : ℝ) :
    V22.G lambda = V22.rootMap lambda * V22.G1 lambda := by
  have hs : 0 < 1 + V22.rootMap lambda := by
    linarith only [shared_rootMap_gt_neg_one lambda]
  unfold V22.G V22.G1
  field_simp [hs.ne'] <;> ring

theorem fiber_hasDerivAt_outer_raw_U {N y : ℝ} (hN : 17 ≤ N)
    (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) (t : ℝ) :
    HasDerivAt (fiberOuterRawU N t) (fiberOuterRawUPrime N t y) y := by
  have hr : 0 < fiberOuterR N y := by
    linarith only [fiber_outer_R_pos hN hy0 hyh]
  have hy : y < 1 := by linarith only [hyh]
  have hp := fiber_hasDerivAt_outer_P (by linarith only [hN]) hy
  have hd := fiber_hasDerivAt_outer_Delta (N := N) hy
  have hR := fiber_hasDerivAt_outer_R hN hy
  have hg := (shared_hasDerivAt_G ((5 / 2 : ℝ) * Real.log t + fiberOuterP N y)).comp y
    (hp.const_add ((5 / 2 : ℝ) * Real.log t))
  have hq := (hasDerivAt_const y (2 : ℝ)).div hR hr.ne'
  have h := (hd.const_add 1).sub (hq.mul hg)
  convert h using 1
  · funext x
    dsimp [fiberOuterRawU]
  · dsimp [fiberOuterRawUPrime]
    rw [fiber_outer_G_root_identity]
    field_simp [hr.ne']
    ring

theorem fiber_outer_raw_UPrime_positive {N y : ℝ} (hN : 17 ≤ N)
    (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) (t : ℝ)
    (hl : (5 / 2 : ℝ) * Real.log t + fiberOuterP N y ≤ 0) :
    0 < fiberOuterRawUPrime N t y := by
  let lambda := (5 / 2 : ℝ) * Real.log t + fiberOuterP N y
  have hr : 0 < fiberOuterR N y := by
    linarith only [fiber_outer_R_pos hN hy0 hyh]
  have hrp : fiberOuterRPrime N y < 0 :=
    fiber_outer_RPrime_negative hN (by linarith only [hyh])
  have hs : -1 ≤ V22.rootMap lambda := (shared_rootMap_gt_neg_one lambda).le
  have hg1 : V22.G1 lambda ≤ 0 := by
    simpa only [shared_G1_zero] using shared_G1_monotone hl
  have hc : fiberOuterRPrime N y / fiberOuterR N y ≤ 0 :=
    (div_neg_of_neg_of_pos hrp hr).le
  have hsr := mul_le_mul_of_nonpos_right hs hc
  have he : (-1 : ℝ) * (fiberOuterRPrime N y / fiberOuterR N y) =
      -fiberOuterRPrime N y / fiberOuterR N y := by ring
  rw [he] at hsr
  have hb : 0 < fiberOuterPPrimeM (N + 1) y -
      V22.rootMap lambda * fiberOuterRPrime N y / fiberOuterR N y := by
    have hP := (fiber_outer_gain_slope_dominates_rate hN hy0 hyh).2
    simp only [mul_div_assoc] at hsr ⊢
    linarith only [hP,hsr]
  have hf : 0 ≤ -2 * V22.G1 lambda / fiberOuterR N y := by
    exact div_nonneg (mul_nonneg_of_nonpos_of_nonpos (by norm_num) hg1) hr.le
  have hm := mul_nonneg hf hb.le
  have hd := fiber_outer_DeltaPrime_positive hN (by linarith only [hyh])
  dsimp [fiberOuterRawUPrime]
  change 0 < fiberOuterDeltaPrime N y +
    (-2 * V22.G1 lambda / fiberOuterR N y) *
      (fiberOuterPPrimeM (N + 1) y - V22.rootMap lambda * fiberOuterRPrime N y / fiberOuterR N y)
  linarith only [hm,hd]

theorem fiber_outer_U_raw_on_nonpos {N y t : ℝ}
    (hl : (5 / 2 : ℝ) * Real.log t + fiberOuterP N y ≤ 0) :
    fiberOuterU N y t = fiberOuterRawU N t y := by
  unfold fiberOuterU fiberOuterRawU
  rw [min_eq_right hl]

theorem fiber_outer_U_nonneg_branch {N y t : ℝ}
    (hl : 0 ≤ (5 / 2 : ℝ) * Real.log t + fiberOuterP N y) :
    fiberOuterU N y t = 1 + fiberOuterDelta N y := by
  unfold fiberOuterU
  rw [min_eq_left hl, shared_G_zero]
  ring

theorem fiber_outer_U_derivatives_agree_at_join {N y : ℝ} (hN : 17 ≤ N)
    (hy0 : 0 ≤ y) (hyh : y ≤ 4 / 25) (t : ℝ)
    (hl : (5 / 2 : ℝ) * Real.log t + fiberOuterP N y = 0) :
    HasDerivAt (fiberOuterRawU N t) (fiberOuterDeltaPrime N y) y ∧
      HasDerivAt (fun x => 1 + fiberOuterDelta N x) (fiberOuterDeltaPrime N y) y := by
  have hp : fiberOuterRawUPrime N t y = fiberOuterDeltaPrime N y := by
    simp only [fiberOuterRawUPrime,hl,shared_G1_zero,zero_mul,mul_zero,zero_div,add_zero]
  exact ⟨hp ▸ fiber_hasDerivAt_outer_raw_U hN hy0 hyh t,
    (fiber_hasDerivAt_outer_Delta (N := N) (by linarith only [hyh])).const_add 1⟩

theorem fiber_outer_U_increases_y {N : ℝ} (hN : 17 ≤ N) (t : ℝ) :
    StrictMonoOn (fun y => fiberOuterU N y t) (Icc 0 (4 / 25 : ℝ)) := by
  intro x hx y hy hxy
  change fiberOuterU N x t < fiberOuterU N y t
  have hd := fiber_outer_Delta_increases_y hN hx hy hxy
  by_cases hly : (5 / 2 : ℝ) * Real.log t + fiberOuterP N y ≤ 0
  · have hraw : StrictMonoOn (fiberOuterRawU N t) (Icc x y) := by
      apply strictMonoOn_of_hasDerivWithinAt_pos (f' := fiberOuterRawUPrime N t) (convex_Icc _ _)
      · intro z hz
        have hz' : z ∈ Icc 0 (4 / 25 : ℝ) := ⟨hx.1.trans hz.1,hz.2.trans hy.2⟩
        exact (fiber_hasDerivAt_outer_raw_U hN hz'.1 hz'.2 t).continuousAt.continuousWithinAt
      · intro z hz
        have hz' : z ∈ Icc x y := interior_subset hz
        exact (fiber_hasDerivAt_outer_raw_U hN (hx.1.trans hz'.1) (hz'.2.trans hy.2) t).hasDerivWithinAt
      · intro z hz
        have hz' : z ∈ Icc x y := interior_subset hz
        have hz0 := hx.1.trans hz'.1
        have hzh := hz'.2.trans hy.2
        have hP := (fiber_outer_P_increases_y hN).monotoneOn ⟨hz0,hzh⟩ hy hz'.2
        exact fiber_outer_raw_UPrime_positive hN hz0 hzh t (by linarith only [hP,hly])
    have hlx : (5 / 2 : ℝ) * Real.log t + fiberOuterP N x ≤ 0 := by
      have hP := (fiber_outer_P_increases_y hN).monotoneOn hx hy hxy.le
      linarith only [hP,hly]
    rw [fiber_outer_U_raw_on_nonpos hlx,fiber_outer_U_raw_on_nonpos hly]
    exact hraw (by exact ⟨le_rfl,hxy.le⟩) (by exact ⟨hxy.le,le_rfl⟩) hxy
  · have hl : 0 ≤ (5 / 2 : ℝ) * Real.log t + fiberOuterP N y := (lt_of_not_ge hly).le
    have hr : 0 < fiberOuterR N x := by linarith only [fiber_outer_R_pos hN hx.1 hx.2]
    have hg := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.le)
      (shared_G_nonneg (min 0 ((5 / 2 : ℝ) * Real.log t + fiberOuterP N x)))
    rw [fiber_outer_U_nonneg_branch hl]
    unfold fiberOuterU
    linarith only [hg,hd]

end Erdos993Lean.Analytic.V213
