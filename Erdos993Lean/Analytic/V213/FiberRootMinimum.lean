module

public import Erdos993Lean.Analytic.V213.FiberRootCalculus

/-!
Literal Eq67: actual H, its unique real minimum and constrained minimum.
P,B,R are strictly positive and gamma is arbitrary real. The accepted
RootMap minimum is reused, its uniqueness is proved by strict derivative
signs, and both closed constrained cases are discharged analytically.
The balance/derivative sign proof follows the earlier RootMap
source, strengthening its weak monotonicity without altering that module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberScalarH (P B R gamma w : ℝ) : ℝ :=
  P * (gamma - w) * Real.exp (-R * w / 2) + B * w

noncomputable def fiberScalarOmega (P B R gamma : ℝ) : ℝ :=
  Real.log (B * Real.exp (R * gamma / 2) / P)

noncomputable def fiberScalarArgmin (P B R gamma : ℝ) : ℝ :=
  gamma - 2 * V22.rootMap (fiberScalarOmega P B R gamma) / R

theorem fiber_H_minimum_value {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma : ℝ) :
    fiberScalarH P B R gamma (fiberScalarArgmin P B R gamma) =
      B * (gamma - 2 / R * V22.G (fiberScalarOmega P B R gamma)) := by
  simpa only [fiberScalarH, fiberScalarArgmin, fiberScalarOmega, shared_rootMap_eq,
    shared_G_eq, rootMinorant, rootMinorantArgmin] using rootMinorant_argmin_value hP hB hR gamma

theorem fiber_H_minimum_bound {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma w : ℝ) :
    B * (gamma - 2 / R * V22.G (fiberScalarOmega P B R gamma)) ≤
      fiberScalarH P B R gamma w := by
  simpa only [fiberScalarH, fiberScalarOmega, shared_G_eq, rootMinorant] using
    rootMinorant_lower_bound hP hB hR gamma w

theorem fiber_H_minimum {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma : ℝ) :
    IsLeast (Set.range (fiberScalarH P B R gamma))
      (B * (gamma - 2 / R * V22.G (fiberScalarOmega P B R gamma))) := by
  constructor
  · exact ⟨fiberScalarArgmin P B R gamma, fiber_H_minimum_value hP hB hR gamma⟩
  · rintro b ⟨w, rfl⟩
    exact fiber_H_minimum_bound hP hB hR gamma w

theorem fiber_exp_one_add_strict {s t : ℝ} (hs : -1 < s) (hst : s < t) :
    Real.exp s * (1 + s) < Real.exp t * (1 + t) := by
  calc
    _ < Real.exp s * (1 + t) := mul_lt_mul_of_pos_left (by linarith) (Real.exp_pos s)
    _ ≤ Real.exp t * (1 + t) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hst.le) (by linarith)

theorem fiber_H_balance {P B R gamma : ℝ} (hP : 0 < P) (hB : 0 < B) :
    P * Real.exp (-R * gamma / 2) *
      (Real.exp (V22.rootMap (fiberScalarOmega P B R gamma)) *
        (1 + V22.rootMap (fiberScalarOmega P B R gamma))) = B := by
  have hs : 0 < 1 + V22.rootMap (fiberScalarOmega P B R gamma) := by
    linarith [shared_rootMap_gt_neg_one (fiberScalarOmega P B R gamma)]
  have ha : 0 < B * Real.exp (R * gamma / 2) / P := by positivity
  have he := congrArg Real.exp (shared_rootMap_equation (fiberScalarOmega P B R gamma))
  rw [Real.exp_add, Real.exp_log hs] at he
  unfold fiberScalarOmega at he
  rw [Real.exp_log ha] at he
  unfold fiberScalarOmega
  rw [he]
  have hc : Real.exp (-R * gamma / 2) * Real.exp (R * gamma / 2) = 1 := by
    rw [← Real.exp_add, show -R * gamma / 2 + R * gamma / 2 = 0 by ring, Real.exp_zero]
  calc
    _ = B * (Real.exp (-R * gamma / 2) * Real.exp (R * gamma / 2)) := by field_simp [hP.ne']
    _ = B := by rw [hc, mul_one]

theorem fiber_H_strict_sides {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma : ℝ) :
    StrictAntiOn (fiberScalarH P B R gamma) (Iic (fiberScalarArgmin P B R gamma)) ∧
      StrictMonoOn (fiberScalarH P B R gamma) (Ici (fiberScalarArgmin P B R gamma)) := by
  let s := V22.rootMap (fiberScalarOmega P B R gamma)
  let C := P * Real.exp (-R * gamma / 2)
  let d : ℝ → ℝ := fun w => B - C * (Real.exp (R * (gamma - w) / 2) * (1 + R * (gamma - w) / 2))
  have hs : -1 < s := shared_rootMap_gt_neg_one _
  have hC : 0 < C := by dsimp [C]; positivity
  have hb : C * (Real.exp s * (1 + s)) = B := fiber_H_balance hP hB
  have hd : ∀ w, HasDerivAt (fiberScalarH P B R gamma) (d w) w :=
    hasDerivAt_rootMinorant P B R gamma
  have hc : Continuous (fiberScalarH P B R gamma) :=
    continuous_iff_continuousAt.mpr (fun w => (hd w).continuousAt)
  have hsig : R * (gamma - fiberScalarArgmin P B R gamma) / 2 = s := by
    dsimp [fiberScalarArgmin, s]
    field_simp [hR.ne']
    ring
  constructor
  · apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Iic _) hc.continuousOn
      (fun w _ => (hd w).hasDerivWithinAt)
    intro w hw
    have hw' : w < fiberScalarArgmin P B R gamma := by simpa only [interior_Iic, mem_Iio] using hw
    have hst : s < R * (gamma - w) / 2 := by
      nlinarith [mul_pos hR (sub_pos.mpr hw')]
    have hm := mul_lt_mul_of_pos_left (fiber_exp_one_add_strict hs hst) hC
    dsimp [d]
    linarith
  · apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici _) hc.continuousOn
      (fun w _ => (hd w).hasDerivWithinAt)
    intro w hw
    have hw' : fiberScalarArgmin P B R gamma < w := by simpa only [interior_Ici, mem_Ioi] using hw
    have hst : R * (gamma - w) / 2 < s := by
      nlinarith [mul_pos hR (sub_pos.mpr hw')]
    by_cases hlo : -1 < R * (gamma - w) / 2
    · have hm := mul_lt_mul_of_pos_left (fiber_exp_one_add_strict hlo hst) hC
      dsimp [d]
      linarith
    · have hf : Real.exp (R * (gamma - w) / 2) * (1 + R * (gamma - w) / 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) (by linarith)
      have hm := mul_nonpos_of_nonneg_of_nonpos hC.le hf
      dsimp [d]
      linarith

theorem fiber_H_unique_minimum {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma w : ℝ) :
    fiberScalarH P B R gamma w = B * (gamma - 2 / R * V22.G (fiberScalarOmega P B R gamma)) ↔
      w = fiberScalarArgmin P B R gamma := by
  rw [← fiber_H_minimum_value hP hB hR gamma]
  constructor
  · intro he
    obtain ⟨ha, hm⟩ := fiber_H_strict_sides hP hB hR gamma
    rcases lt_trichotomy w (fiberScalarArgmin P B R gamma) with hw | hw | hw
    · have hh := ha (by exact hw.le) (by exact le_refl _) hw
      exact False.elim (by rw [he] at hh; exact lt_irrefl _ hh)
    · exact hw
    · have hh := hm (by exact le_refl _) (by exact hw.le) hw
      exact False.elim (by rw [he] at hh; exact lt_irrefl _ hh)
  · rintro rfl
    rfl

theorem fiber_H_constrained_minimum {P B R : ℝ} (hP : 0 < P) (hB : 0 < B)
    (hR : 0 < R) (gamma : ℝ) :
    IsLeast ((fiberScalarH P B R gamma) '' Ici gamma)
      (B * (gamma - 2 / R * V22.G (min 0 (fiberScalarOmega P B R gamma)))) := by
  by_cases ho : fiberScalarOmega P B R gamma ≤ 0
  · rw [min_eq_right ho]
    have hs : V22.rootMap (fiberScalarOmega P B R gamma) ≤ 0 := by
      simpa only [shared_rootMap_zero] using shared_rootMap_monotone ho
    have hw : gamma ≤ fiberScalarArgmin P B R gamma := by
      unfold fiberScalarArgmin
      have hh : 2 * V22.rootMap (fiberScalarOmega P B R gamma) / R ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hR.le
      linarith
    constructor
    · exact ⟨fiberScalarArgmin P B R gamma, hw, fiber_H_minimum_value hP hB hR gamma⟩
    · rintro b ⟨w, _, rfl⟩
      exact fiber_H_minimum_bound hP hB hR gamma w
  · have ho' : 0 ≤ fiberScalarOmega P B R gamma := le_of_lt (lt_of_not_ge ho)
    rw [min_eq_left ho', shared_G_zero]
    simp only [mul_zero, sub_zero]
    have hs : 0 ≤ V22.rootMap (fiberScalarOmega P B R gamma) := by
      simpa only [shared_rootMap_zero] using shared_rootMap_monotone ho'
    have hw : fiberScalarArgmin P B R gamma ≤ gamma := by
      unfold fiberScalarArgmin
      have hh : 0 ≤ 2 * V22.rootMap (fiberScalarOmega P B R gamma) / R := by positivity
      linarith
    constructor
    · exact ⟨gamma, le_refl _, by simp [fiberScalarH]⟩
    · rintro b ⟨w, hgw, rfl⟩
      have hm := (fiber_H_strict_sides hP hB hR gamma).2.monotoneOn
      have hh := hm hw (hw.trans hgw) hgw
      simpa [fiberScalarH] using hh

end Erdos993Lean.Analytic.V213
