module

public import Erdos993Lean.Analytic.V22.Analysis.SharedRoot
public import Mathlib.Analysis.Convex.Deriv

/-!
Lemma6.11: the genuine inverse-root change of variables and its convex
endpoint derivative. All formulas use the accepted everywhere-defined
rootMap; zero argument and the closed endpoint are included.
No generated family or paper lemma is assumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberEndpointLambda (p t : ℝ) : ℝ := 5 / 2 * Real.log t + p

noncomputable def fiberEndpointStart (p : ℝ) : ℝ := Real.exp (-2 * p / 5)

noncomputable def fiberEndpointZ (p t : ℝ) : ℝ := 1 + V22.rootMap (fiberEndpointLambda p t)

noncomputable def fiberEndpointJ (p t : ℝ) : ℝ := t * (1 - fiberEndpointZ p t) / fiberEndpointZ p t

noncomputable def fiberEndpointJPrime (p t : ℝ) : ℝ :=
  -(fiberEndpointZ p t ^ 2 + 3 / 2) / (fiberEndpointZ p t * (1 + fiberEndpointZ p t))

noncomputable def fiberEndpointJSecond (p t : ℝ) : ℝ :=
  (-fiberEndpointZ p t ^ 2 + 3 * fiberEndpointZ p t + 3 / 2) /
    (fiberEndpointZ p t ^ 2 * (1 + fiberEndpointZ p t) ^ 2) *
      (5 * fiberEndpointZ p t / (2 * t * (1 + fiberEndpointZ p t)))

theorem fiber_endpoint_start_pos (p : ℝ) : 0 < fiberEndpointStart p := Real.exp_pos _

theorem fiber_endpoint_start_lambda (p : ℝ) :
    fiberEndpointLambda p (fiberEndpointStart p) = 0 := by
  unfold fiberEndpointLambda fiberEndpointStart
  rw [Real.log_exp]
  ring

theorem fiber_endpoint_z_pos (p t : ℝ) : 0 < fiberEndpointZ p t := by
  unfold fiberEndpointZ
  linarith [shared_rootMap_gt_neg_one (fiberEndpointLambda p t)]

theorem fiber_endpoint_z_start (p : ℝ) : fiberEndpointZ p (fiberEndpointStart p) = 1 := by
  simp [fiberEndpointZ, fiber_endpoint_start_lambda]

theorem fiber_endpoint_lambda_nonpos {p t : ℝ} (ht : 0 < t)
    (hstart : t ≤ fiberEndpointStart p) : fiberEndpointLambda p t ≤ 0 := by
  have h := Real.log_le_log ht hstart
  unfold fiberEndpointStart at h
  rw [Real.log_exp] at h
  unfold fiberEndpointLambda
  linarith

theorem fiber_endpoint_z_le_one {p t : ℝ} (ht : 0 < t)
    (hstart : t ≤ fiberEndpointStart p) : fiberEndpointZ p t ≤ 1 := by
  have h := shared_rootMap_monotone (fiber_endpoint_lambda_nonpos ht hstart)
  simpa [fiberEndpointZ] using (by
    rw [shared_rootMap_zero] at h
    linarith : 1 + V22.rootMap (fiberEndpointLambda p t) ≤ (1 : ℝ))

theorem fiber_hasDerivAt_endpoint_lambda {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointLambda p) ((5 / 2 : ℝ) / t) t := by
  convert ((((hasDerivAt_id t).log ht.ne').const_mul (5 / 2 : ℝ)).add_const p) using 1
  · rfl
  · dsimp
    ring

theorem fiber_hasDerivAt_endpoint_z {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointZ p)
      (5 * fiberEndpointZ p t / (2 * t * (1 + fiberEndpointZ p t))) t := by
  have hz := fiber_endpoint_z_pos p t
  have hs : 0 < 2 + V22.rootMap (fiberEndpointLambda p t) := by
    linarith [shared_rootMap_gt_neg_one (fiberEndpointLambda p t)]
  have h := ((shared_hasDerivAt_rootMap (fiberEndpointLambda p t)).comp t
    (fiber_hasDerivAt_endpoint_lambda ht)).const_add 1
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberEndpointZ]
    rw [show 1 + (1 + V22.rootMap (fiberEndpointLambda p t)) =
      2 + V22.rootMap (fiberEndpointLambda p t) by ring]
    field_simp [ht.ne', hs.ne'] <;> ring

theorem fiber_hasDerivAt_endpoint_J {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointJ p) (fiberEndpointJPrime p t) t := by
  have hz := fiber_endpoint_z_pos p t
  have h := ((hasDerivAt_id t).mul
    ((hasDerivAt_const t (1 : ℝ)).sub (fiber_hasDerivAt_endpoint_z (p := p) ht))).div
      (fiber_hasDerivAt_endpoint_z (p := p) ht) hz.ne'
  convert h using 1
  · funext x
    rfl
  · dsimp [fiberEndpointJPrime]
    field_simp [ht.ne', hz.ne', ne_of_gt (by linarith : 0 < 1 + fiberEndpointZ p t)] <;> ring

theorem fiber_hasDerivAt_endpoint_JPrime {p t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberEndpointJPrime p) (fiberEndpointJSecond p t) t := by
  have hz := fiber_endpoint_z_pos p t
  have hd := fiber_hasDerivAt_endpoint_z (p := p) ht
  have h := (((hd.pow 2).add_const (3 / 2 : ℝ)).div
    (hd.mul (hd.const_add 1)) (by positivity : fiberEndpointZ p t * (1 + fiberEndpointZ p t) ≠ 0)).neg
  convert h using 1
  · funext x
    dsimp [fiberEndpointJPrime]
    ring
  · dsimp [fiberEndpointJSecond]
    field_simp [ht.ne', hz.ne', ne_of_gt (by linarith : 0 < 1 + fiberEndpointZ p t)] <;> ring

theorem fiber_endpoint_JSecond_pos {p t : ℝ} (ht : 0 < t)
    (hstart : t ≤ fiberEndpointStart p) : 0 < fiberEndpointJSecond p t := by
  have hz := fiber_endpoint_z_pos p t
  have hz1 := fiber_endpoint_z_le_one ht hstart
  have hn : 0 < -fiberEndpointZ p t ^ 2 + 3 * fiberEndpointZ p t + 3 / 2 := by nlinarith
  unfold fiberEndpointJSecond
  positivity

theorem fiber_endpoint_J_convex {p a : ℝ} (ha : 0 < a) :
    ConvexOn ℝ (Icc a (fiberEndpointStart p)) (fiberEndpointJ p) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fiberEndpointJPrime p)
    (f'' := fiberEndpointJSecond p) (convex_Icc _ _)
  · intro t ht
    exact (fiber_hasDerivAt_endpoint_J (lt_of_lt_of_le ha ht.1)).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    exact (fiber_hasDerivAt_endpoint_J (ha.trans ht'.1)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    exact (fiber_hasDerivAt_endpoint_JPrime (ha.trans ht'.1)).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Ioo a (fiberEndpointStart p) := by simpa only [interior_Icc] using ht
    exact (fiber_endpoint_JSecond_pos (ha.trans ht'.1) ht'.2.le).le

end Erdos993Lean.Analytic.V213
