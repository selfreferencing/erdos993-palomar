module

public import Erdos993Lean.Analytic.V213.FiberNegativeRoot

/-!
Literal Eq80: G(-v)<=v^2/(4-v+v^2/48) on the closed interval[0,3].
The displayed rational barrier is compared through the smooth actual
inverse-root function, including zero. Every derivative and polynomial
sign is proved; no finite numerical premise replaces the source bound.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberBarrierDenom (v : ℝ) : ℝ := 4 - v + v ^ 2 / 48

noncomputable def fiberBarrierT (v : ℝ) : ℝ := v / Real.sqrt (fiberBarrierDenom v)

noncomputable def fiberBarrierTPrime (v : ℝ) : ℝ :=
  (4 - v / 2) / (fiberBarrierDenom v * Real.sqrt (fiberBarrierDenom v))

theorem fiber_barrier_denom_bound {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    1 ≤ fiberBarrierDenom v := by
  unfold fiberBarrierDenom
  nlinarith [sq_nonneg v]

theorem fiber_hasDerivAt_barrier_t {v : ℝ} (hd : 0 < fiberBarrierDenom v) :
    HasDerivAt fiberBarrierT (fiberBarrierTPrime v) v := by
  have hS := Real.sqrt_pos.2 hd
  have hsq := Real.sq_sqrt hd.le
  have hD : HasDerivAt fiberBarrierDenom (-1 + v / 24) v := by
    convert (((hasDerivAt_const v (4 : ℝ)).sub (hasDerivAt_id v)).add
      (((hasDerivAt_id v).pow 2).div_const 48)) using 1
    · funext y; dsimp [fiberBarrierDenom]
    · dsimp; ring
  convert (hasDerivAt_id v).div (hD.sqrt hd.ne') hS.ne' using 1
  · rfl
  · dsimp
    unfold fiberBarrierTPrime
    field_simp [hS.ne', hd.ne']
    rw [hsq]
    unfold fiberBarrierDenom
    ring

theorem fiber_barrier_polynomial_signs {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    0 < 16 - 6 * v + v ^ 2 - v ^ 3 / 48 ∧
      0 < 1 / 3 - 3 * v / 64 + v ^ 2 / 768 - v ^ 3 / 110592 := by
  have h3 := pow_le_pow_left₀ hv0 hv3 3
  norm_num at h3
  constructor
  · nlinarith [sq_nonneg (v - 3)]
  · nlinarith [sq_nonneg v]

theorem fiber_barrier_slope_bounds {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    0 ≤ 4 * fiberBarrierTPrime v - fiberBarrierT v ∧
      4 * fiberBarrierTPrime v ^ 2 - 2 * fiberBarrierT v * fiberBarrierTPrime v - 1 ≥ 0 := by
  have hd : 0 < fiberBarrierDenom v := by linarith [fiber_barrier_denom_bound hv0 hv3]
  have hs := Real.sqrt_pos.2 hd
  have hsq := Real.sq_sqrt hd.le
  have hp := fiber_barrier_polynomial_signs hv0 hv3
  have hi : 4 * fiberBarrierTPrime v - fiberBarrierT v =
      (16 - 6 * v + v ^ 2 - v ^ 3 / 48) /
        (fiberBarrierDenom v * Real.sqrt (fiberBarrierDenom v)) := by
    unfold fiberBarrierTPrime fiberBarrierT
    field_simp [hd.ne', hs.ne']
    unfold fiberBarrierDenom
    ring
  have hj : 4 * fiberBarrierTPrime v ^ 2 - 2 * fiberBarrierT v * fiberBarrierTPrime v - 1 =
      v ^ 3 * (1 / 3 - 3 * v / 64 + v ^ 2 / 768 - v ^ 3 / 110592) /
        (fiberBarrierDenom v ^ 3) := by
    unfold fiberBarrierTPrime fiberBarrierT
    field_simp [hd.ne', hs.ne']
    rw [hsq]
    unfold fiberBarrierDenom
    ring
  constructor
  · rw [hi]
    exact div_nonneg hp.1.le (mul_pos hd hs).le
  · rw [hj]
    exact div_nonneg (mul_nonneg (pow_nonneg hv0 3) hp.2.le) (pow_pos hd 3).le

theorem fiber_barrier_sqrt_slope {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    fiberBarrierT v + Real.sqrt (fiberBarrierT v ^ 2 + 4) ≤ 4 * fiberBarrierTPrime v := by
  have h := fiber_barrier_slope_bounds hv0 hv3
  have hs : Real.sqrt (fiberBarrierT v ^ 2 + 4) ≤ 4 * fiberBarrierTPrime v - fiberBarrierT v := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact h.1
    · nlinarith
  linarith

theorem fiber_barrier_inverse_slope {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    (fiberBarrierT v - Real.sqrt (fiberBarrierT v ^ 2 + 4)) * fiberBarrierTPrime v + 1 ≤ 0 := by
  have hz := fiber_negative_z_pos (fiberBarrierT v)
  have hs := fiber_barrier_sqrt_slope hv0 hv3
  have hprod := mul_le_mul_of_nonneg_left hs hz.le
  have he : fiberNegativeZ (fiberBarrierT v) *
      (fiberBarrierT v + Real.sqrt (fiberBarrierT v ^ 2 + 4)) = 2 := by
    have hh := Real.sq_sqrt (by positivity : 0 ≤ fiberBarrierT v ^ 2 + 4)
    unfold fiberNegativeZ
    nlinarith
  rw [he] at hprod
  unfold fiberNegativeZ at hprod
  nlinarith

theorem fiber_barrier_inverse_bound {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    fiberNegativeInverse (fiberBarrierT v) ≤ -v := by
  let f : ℝ → ℝ := fun x => fiberNegativeInverse (fiberBarrierT x) + x
  let d : ℝ → ℝ := fun x =>
    (fiberBarrierT x - Real.sqrt (fiberBarrierT x ^ 2 + 4)) * fiberBarrierTPrime x + 1
  have hd : ∀ x ∈ Icc (0 : ℝ) 3, HasDerivAt f (d x) x := by
    intro x hx
    have hD : 0 < fiberBarrierDenom x := by linarith [fiber_barrier_denom_bound hx.1 hx.2]
    exact ((fiber_hasDerivAt_negative_inverse (fiberBarrierT x)).comp x
      (fiber_hasDerivAt_barrier_t hD)).add (hasDerivAt_id x)
  have hc : ContinuousOn f (Icc (0 : ℝ) 3) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have ha : AntitoneOn f (Icc (0 : ℝ) 3) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _) hc
      (fun x hx => (hd x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hx' := interior_subset hx
    exact fiber_barrier_inverse_slope hx'.1 hx'.2
  have hh := ha (by norm_num) ⟨hv0, hv3⟩ hv0
  have hzero : fiberBarrierT 0 = 0 := by norm_num [fiberBarrierT, fiberBarrierDenom]
  dsimp [f] at hh
  rw [hzero, fiber_negative_inverse_zero] at hh
  linarith

theorem fiber_negative_root_barrier {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    V22.G (-v) ≤ v ^ 2 / (4 - v + v ^ 2 / 48) := by
  have hb := fiber_barrier_inverse_bound hv0 hv3
  have hgv := shared_G_antitoneOn_nonpos (by linarith : fiberNegativeInverse (fiberBarrierT v) ≤ 0)
    (by linarith : -v ≤ 0) hb
  rw [fiber_negative_inverse_G] at hgv
  have hd : 0 < fiberBarrierDenom v := by linarith [fiber_barrier_denom_bound hv0 hv3]
  unfold fiberBarrierT at hgv
  rw [div_pow, Real.sq_sqrt hd.le] at hgv
  simpa only [fiberBarrierDenom] using hgv

end Erdos993Lean.Analytic.V213
