module

public import Erdos993Lean.Analytic.V213.FiberProfileDefinitions
public import Mathlib.Analysis.Convex.Deriv

/-!
Inverse root geometry. T is the actual exp/log realization of
(exp(-a)*(1-a))^(2/5); its actual first/second derivatives, strict
decrease and concavity give the complete tangent-line transfer.
No finite line is consumed here.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set
open Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberProfileT (a : ℝ) : ℝ :=
  Real.exp ((2 / 5 : ℝ) * (-a + Real.log (1 - a)))

noncomputable def fiberProfileTPrime (a : ℝ) : ℝ :=
  -(2 / 5) * (2 - a) / (1 - a) * fiberProfileT a

noncomputable def fiberProfileTSecond (a : ℝ) : ℝ :=
  fiberProfileT a * (4 * (2 - a) ^ 2 / 25 - 2 / 5) / (1 - a) ^ 2

noncomputable def fiberProfileTangentK (v : ℝ) : ℝ := 5 * (1 - v) / (2 * (2 - v))

theorem fiber_profile_T_positive (a : ℝ) : 0 < fiberProfileT a := Real.exp_pos _

theorem fiber_profile_T_printed {a : ℝ} (ha : a < 1) :
    fiberProfileT a = (Real.exp (-a) * (1 - a)) ^ (2 / 5 : ℝ) := by
  have hd : 0 < 1 - a := by linarith only [ha]
  rw [Real.rpow_def_of_pos (mul_pos (Real.exp_pos _) hd),Real.log_mul
    (Real.exp_ne_zero _) hd.ne',Real.log_exp]
  unfold fiberProfileT
  congr 1
  ring

theorem fiber_profile_T_actual {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    fiberProfileT (fiberRayAroot t) = t := by
  have h := (fiber_ray_root_formulas ht ht1).2.1
  have he := shared_rootMap_equation (5 / 2 * Real.log t)
  have hid : -fiberRayAroot t + Real.log (1 - fiberRayAroot t) = 5 / 2 * Real.log t := by
    simpa only [fiberRayAroot,neg_neg,sub_neg_eq_add] using he
  unfold fiberProfileT
  rw [hid]
  convert Real.exp_log ht using 1 <;> ring

theorem fiber_profile_T_hasDerivAt {a : ℝ} (ha : a < 1) :
    HasDerivAt fiberProfileT (fiberProfileTPrime a) a := by
  have hd : 1 - a ≠ 0 := by linarith only [ha]
  have hl := (((hasDerivAt_id a).neg).add
    (((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)).log hd)).const_mul (2 / 5 : ℝ)
  convert hl.exp using 1
  · funext x
    rfl
  · dsimp [fiberProfileTPrime,fiberProfileT]
    field_simp [hd]
    ring

theorem fiber_profile_TPrime_hasDerivAt {a : ℝ} (ha : a < 1) :
    HasDerivAt fiberProfileTPrime (fiberProfileTSecond a) a := by
  have hd : 1 - a ≠ 0 := by linarith only [ha]
  have hq := (((hasDerivAt_const a (2 : ℝ)).sub (hasDerivAt_id a)).div
    ((hasDerivAt_const a (1 : ℝ)).sub (hasDerivAt_id a)) hd).const_mul (-(2 / 5 : ℝ))
  convert hq.mul (fiber_profile_T_hasDerivAt ha) using 1
  · funext x
    dsimp [fiberProfileTPrime]
    ring
  · dsimp [fiberProfileTSecond,fiberProfileTPrime]
    field_simp [hd]
    ring

theorem fiber_profile_TPrime_negative {a : ℝ} (ha : a < 1) : fiberProfileTPrime a < 0 := by
  have hd : 0 < 1 - a := by linarith only [ha]
  have hn : 0 < 2 - a := by linarith only [ha]
  unfold fiberProfileTPrime
  exact mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (by norm_num : -(2 / 5 : ℝ) < 0) hn) hd)
    (fiber_profile_T_positive _)

theorem fiber_profile_T_decreases : StrictAntiOn fiberProfileT (Iio (1 : ℝ)) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (f' := fiberProfileTPrime) (convex_Iio _)
  · intro a ha
    exact (fiber_profile_T_hasDerivAt ha).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : a ∈ Iio (1 : ℝ) := interior_subset ha
    exact (fiber_profile_T_hasDerivAt ha').hasDerivWithinAt
  · intro a ha
    have ha' : a ∈ Iio (1 : ℝ) := interior_subset ha
    exact fiber_profile_TPrime_negative ha'

theorem fiber_profile_TSecond_negative {a : ℝ} (ha : 1 / 2 ≤ a) (ha1 : a < 1) :
    fiberProfileTSecond a < 0 := by
  have hd : 0 < (1 - a) ^ 2 := sq_pos_of_pos (by linarith only [ha1])
  have hn : 4 * (2 - a) ^ 2 / 25 - 2 / 5 ≤ -(1 / 25 : ℝ) := by
    nlinarith only [ha,ha1]
  unfold fiberProfileTSecond
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (fiber_profile_T_positive _)
    (by linarith only [hn])) hd

theorem fiber_profile_T_concave : ConcaveOn ℝ (Ico (1 / 2 : ℝ) 1) fiberProfileT := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (f' := fiberProfileTPrime)
    (f'' := fiberProfileTSecond) (convex_Ico _ _)
  · intro a ha
    exact (fiber_profile_T_hasDerivAt ha.2).continuousAt.continuousWithinAt
  · intro a ha
    exact (fiber_profile_T_hasDerivAt (interior_subset ha).2).hasDerivWithinAt
  · intro a ha
    exact (fiber_profile_TPrime_hasDerivAt (interior_subset ha).2).hasDerivWithinAt
  · intro a ha
    have ha' := interior_subset ha
    exact (fiber_profile_TSecond_negative ha'.1 ha'.2).le

theorem fiber_profile_T_tangent {a v : ℝ}
    (ha : a ∈ Ico (1 / 2 : ℝ) 1) (hv : v ∈ Ico (1 / 2 : ℝ) 1) :
    fiberProfileT a ≤ fiberProfileT v + fiberProfileTPrime v * (a - v) := by
  rcases lt_trichotomy a v with hav | rfl | hva
  · have h := fiber_profile_T_concave.le_slope_of_hasDerivAt ha hv hav
      (fiber_profile_T_hasDerivAt hv.2)
    rw [slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hav)).mp h
    linarith only [hh]
  · simp
  · have h := fiber_profile_T_concave.slope_le_of_hasDerivAt hv ha hva
      (fiber_profile_T_hasDerivAt hv.2)
    rw [slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hva)).mp h
    linarith only [hh]

theorem fiber_profile_tangent_K {v : ℝ} (hv : v < 1) :
    0 < fiberProfileTangentK v ∧
      fiberProfileTPrime v = -fiberProfileT v / fiberProfileTangentK v := by
  have h1 : 0 < 1 - v := by linarith only [hv]
  have h2 : 0 < 2 - v := by linarith only [hv]
  constructor
  · unfold fiberProfileTangentK
    positivity
  · unfold fiberProfileTPrime fiberProfileTangentK
    field_simp [h1.ne',h2.ne'] <;> ring

theorem fiber_profile_root_line {t v beta : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (ha : 1 / 2 ≤ fiberRayAroot t) (hv : v ∈ Ico (1 / 2 : ℝ) 1)
    (hbeta : beta < fiberProfileTangentK v / fiberProfileT v) :
    fiberRayAroot t < v + fiberProfileTangentK v - beta * t := by
  have ha1 := (fiber_ray_root_formulas ht ht1).2.1
  have h := fiber_profile_T_tangent ⟨ha,ha1⟩ hv
  have hk := fiber_profile_tangent_K hv.2
  rw [fiber_profile_T_actual ht ht1,hk.2] at h
  have hTv := fiber_profile_T_positive v
  have hmul := (lt_div_iff₀ hTv).mp hbeta
  have hmul' := mul_lt_mul_of_pos_right hmul ht
  have htangent := (le_div_iff₀ hk.1).mp (show t ≤
      (fiberProfileT v * fiberProfileTangentK v - fiberProfileT v * (fiberRayAroot t - v)) /
        fiberProfileTangentK v by
    convert h using 1 <;> field_simp [hk.1.ne'] <;> ring)
  have hfinal : fiberProfileT v * fiberRayAroot t <
      fiberProfileT v * (v + fiberProfileTangentK v - beta * t) := by
    nlinarith only [htangent,hmul']
  exact (mul_lt_mul_iff_right₀ hTv).mp hfinal

end Erdos993Lean.Analytic.V213
