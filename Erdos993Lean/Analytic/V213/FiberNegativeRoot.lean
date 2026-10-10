module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus

/-!
Eq80's smooth inverse parametrization of the actual root map.
It avoids differentiating sqrt(G) at zero. Every identity and derivative
uses genuine log/sqrt functions and is proved for all real h; no numeric
family or inverse equation is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberNegativeZ (h : ℝ) : ℝ := (Real.sqrt (h ^ 2 + 4) - h) / 2

noncomputable def fiberNegativeInverse (h : ℝ) : ℝ :=
  -h * fiberNegativeZ h + 2 * Real.log (fiberNegativeZ h)

theorem fiber_negative_z_pos (h : ℝ) : 0 < fiberNegativeZ h := by
  have hh : 0 ≤ h ^ 2 + 4 := by positivity
  have ha := Real.sq_sqrt hh
  have hs := Real.sqrt_nonneg (h ^ 2 + 4)
  unfold fiberNegativeZ
  nlinarith

theorem fiber_negative_z_equation (h : ℝ) :
    fiberNegativeZ h ^ 2 + h * fiberNegativeZ h = 1 := by
  have ha := Real.sq_sqrt (by positivity : 0 ≤ h ^ 2 + 4)
  unfold fiberNegativeZ
  nlinarith

theorem fiber_hasDerivAt_negative_z (h : ℝ) :
    HasDerivAt fiberNegativeZ ((h / Real.sqrt (h ^ 2 + 4) - 1) / 2) h := by
  have ha : 0 < h ^ 2 + 4 := by positivity
  convert (((((hasDerivAt_id h).pow 2).add_const 4).sqrt ha.ne').sub
    (hasDerivAt_id h)).div_const 2 using 1
  · rfl
  · dsimp
    ring

theorem fiber_hasDerivAt_negative_inverse (h : ℝ) :
    HasDerivAt fiberNegativeInverse (h - Real.sqrt (h ^ 2 + 4)) h := by
  have hz := fiber_negative_z_pos h
  have hA : 0 < Real.sqrt (h ^ 2 + 4) := Real.sqrt_pos.2 (by positivity)
  have hs := Real.sq_sqrt (by positivity : 0 ≤ h ^ 2 + 4)
  have hZne : Real.sqrt (h ^ 2 + 4) - h ≠ 0 := by
    unfold fiberNegativeZ at hz
    linarith
  have hd := fiber_hasDerivAt_negative_z h
  convert (((hasDerivAt_id h).neg.mul hd).add ((hd.log hz.ne').const_mul 2)) using 1
  · funext y
    rfl
  · dsimp
    unfold fiberNegativeZ
    field_simp [hA.ne', hZne]
    nlinarith [mul_self_nonneg h, mul_self_nonneg (Real.sqrt (h ^ 2 + 4)),
      show h * (Real.sqrt (h ^ 2 + 4)) ^ 2 = h * (h ^ 2 + 4) by rw [hs]]

theorem fiber_negative_inverse_zero : fiberNegativeInverse 0 = 0 := by
  norm_num [fiberNegativeInverse, fiberNegativeZ]

theorem fiber_negative_inverse_root (h : ℝ) :
    V22.rootMap (fiberNegativeInverse h) = -h * fiberNegativeZ h := by
  have hz := fiber_negative_z_pos h
  have he := fiber_negative_z_equation h
  have hs : 1 + -h * fiberNegativeZ h = fiberNegativeZ h ^ 2 := by linarith
  have hd : -1 < -h * fiberNegativeZ h := by nlinarith [sq_pos_of_pos hz]
  rw [shared_rootMap_eq]
  apply rootMap_eq_of_equation hd
  unfold rootEquation fiberNegativeInverse
  rw [hs, Real.log_pow]
  norm_num

theorem fiber_negative_inverse_G (h : ℝ) : V22.G (fiberNegativeInverse h) = h ^ 2 := by
  have hz := fiber_negative_z_pos h
  have he := fiber_negative_z_equation h
  unfold V22.G
  rw [fiber_negative_inverse_root,
    show 1 + -h * fiberNegativeZ h = fiberNegativeZ h ^ 2 by linarith]
  field_simp [hz.ne']

end Erdos993Lean.Analytic.V213
