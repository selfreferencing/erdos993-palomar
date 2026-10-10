module

public import Erdos993Lean.Analytic.V213.FiberRayDefinitions
public import Erdos993Lean.Analytic.V213.FiberWindowAnchor

/-!
Literal Eq94--96 profiles. The root argument is explicit, with its
proved bridge to the actual s(5/2 log t). Square-root upper and reciprocal
comparisons transfer the actual D/E ray envelopes to the displayed
rational profiles. No sampled endpoint or unproved continuation is used.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

noncomputable def fiberProfileG0 (a : ℝ) : ℝ := a ^ 2 / (1 - a)

noncomputable def fiberProfileC (cf df a : ℝ) : ℝ :=
  -6 * a - 2 + (df - 11 / 10) * a / (1 - a) + cf / ((1 - a) * (2 - a))

noncomputable def fiberProfileF (t a : ℝ) : ℝ :=
  2 * t * fiberProfileG0 a - 9 / 2 * (1 - t) ^ 2

noncomputable def fiberProfileD (cf df rho kappa m s delta b beta t u a : ℝ) : ℝ :=
  fiberProfileF t a + b + beta * (t - 1) + fiberProfileC cf df a / m +
    2 * fiberProfileG0 a * (m * t + 2 + s ^ 2) / (s * rho * m) * u +
    (m * t + 2) / m * (kappa * fiberProfileG0 a / rho + delta - delta * (m * t + 2)) * u ^ 2

noncomputable def fiberProfileE (t u a : ℝ) : ℝ :=
  fiberProfileF t a + 97 * t * fiberProfileG0 a / (140 * (63 / 100)) * u +
    t * ((17 / 6) * fiberProfileG0 a / (63 / 100) + 1 - 2 * (19 * t + 2)) * u ^ 2

noncomputable def fiberProfileB1 (rho kappa s u : ℝ) : ℝ :=
  2 + (2 * u / s + kappa * u ^ 2) / rho

noncomputable def fiberProfileB0 (rho kappa m s u : ℝ) : ℝ :=
  (2 * (2 + s ^ 2) * u / s + 2 * kappa * u ^ 2) / (rho * m)

noncomputable def fiberProfileEB0 (u : ℝ) : ℝ :=
  2 + 97 * u / (140 * (63 / 100)) + (17 / 6) * u ^ 2 / (63 / 100)

theorem fiber_profile_G0_nonneg {a : ℝ} (ha : a < 1) : 0 ≤ fiberProfileG0 a := by
  unfold fiberProfileG0
  exact div_nonneg (sq_nonneg _) (by linarith only [ha])

theorem fiber_profile_G0_reciprocal {a : ℝ} (ha : a ≠ 1) :
    fiberProfileG0 a = (1 - a) - 2 + 1 / (1 - a) := by
  unfold fiberProfileG0
  have hd : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  field_simp [hd]
  ring

theorem fiber_profile_C_reciprocal {cf df a : ℝ} (ha1 : a ≠ 1) (ha2 : a ≠ 2) :
    fiberProfileC cf df a = -6 * a - 2 + (df - 11 / 10) * (1 / (1 - a) - 1) +
      cf * (1 / (1 - a) - 1 / (2 - a)) := by
  have hd1 : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha1)
  have hd2 : 2 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha2)
  unfold fiberProfileC
  field_simp [hd1,hd2]
  ring

theorem fiber_profile_D_normal {cf df rho kappa m s delta b beta t u a : ℝ}
    (hr : rho ≠ 0) (hm : m ≠ 0) (hs : s ≠ 0) :
    fiberProfileD cf df rho kappa m s delta b beta t u a =
      fiberProfileG0 a * (fiberProfileB1 rho kappa s u * t +
        fiberProfileB0 rho kappa m s u) + fiberProfileC cf df a / m -
        9 / 2 * (1 - t) ^ 2 + b + beta * (t - 1) + delta * u ^ 2 * (-m * t ^ 2 - 3 * t - 2 / m) := by
  unfold fiberProfileD fiberProfileF fiberProfileB1 fiberProfileB0
  field_simp [hr,hm,hs]
  ring

theorem fiber_profile_E_normal (t u a : ℝ) :
    fiberProfileE t u a = t * fiberProfileEB0 u * fiberProfileG0 a -
      9 / 2 * (1 - t) ^ 2 - 3 * t * u ^ 2 - 38 * t ^ 2 * u ^ 2 := by
  unfold fiberProfileE fiberProfileF fiberProfileEB0
  ring

theorem fiber_profile_B_lower {rho kappa m s u : ℝ}
    (hr : 0 < rho) (hk : 0 ≤ kappa) (hm : 0 < m) (hs : 0 < s) (hu : 0 ≤ u) :
    2 ≤ fiberProfileB1 rho kappa s u ∧ 0 ≤ fiberProfileB0 rho kappa m s u := by
  unfold fiberProfileB1 fiberProfileB0
  constructor
  · have h : 0 ≤ (2 * u / s + kappa * u ^ 2) / rho := by positivity
    linarith only [h]
  · positivity

theorem fiber_profile_EB_lower {u : ℝ} (hu : 0 ≤ u) : 2 ≤ fiberProfileEB0 u := by
  unfold fiberProfileEB0
  have h1 : 0 ≤ 97 * u / (140 * (63 / 100 : ℝ)) := by positivity
  have h2 : 0 ≤ (17 / 6 : ℝ) * u ^ 2 / (63 / 100) := by positivity
  linarith only [h1,h2]

theorem fiber_profile_ray_C {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (id : FiberRayIdentity) :
    fiberRayC id t = fiberProfileC (fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f))
      (lowMeanFractionReal (fiberRayById id).d_f) (fiberRayAroot t) := by
  have h := fiber_ray_root_formulas ht ht1
  unfold fiberRayC fiberProfileC
  rw [h.2.2.2.1,h.2.2.2.2]
  ring

/-- Eq90 bounds the actual square-root term of D; g is bounded by the displayed affine target. -/
theorem fiber_profile_ray_D {t m s ra u b beta : ℝ} {g : ℝ → ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hm : 0 < m) (hs : 0 < s) (hu : 0 ≤ u)
    (hg : g t ≤ b + beta * (t - 1)) (id : FiberRayIdentity) :
    fiberRayD id g m t ra u ≤
      fiberProfileD (fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f))
        (lowMeanFractionReal (fiberRayById id).d_f)
        (lowMeanFractionReal (fiberRayById id).rho_f)
        (lowMeanFractionReal (fiberRayById id).k_f) m s (fiberRayDelta ra) b beta t u
        (fiberRayAroot t) := by
  have h := fiber_ray_root_formulas ht ht1
  have hr := (fiber_ray_record_guards id).2.2.2.2.2.1
  have hN : 0 ≤ m * t + 2 := by positivity
  have hsqrt := (fiber_window_anchor_sqrt hN hs).2
  have hG := shared_G_nonneg (5 / 2 * Real.log t)
  have hcoef : 0 ≤ 4 * G (5 / 2 * Real.log t) * u /
      (lowMeanFractionReal (fiberRayById id).rho_f * m) := by
    exact div_nonneg (by positivity) (mul_pos hr hm).le
  have hb := mul_le_mul_of_nonneg_left hsqrt hcoef
  have hC := fiber_profile_ray_C ht ht1 id
  unfold fiberRayD fiberRayH fiberRayHPolynomial fiberRayA fiberRayK fiberRayF
  rw [hC,h.2.2.1]
  unfold fiberProfileD fiberProfileF fiberProfileG0 at *
  have hid :
      (4 * ((fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t)) * u /
        (lowMeanFractionReal (fiberRayById id).rho_f * m)) *
          ((m * t + 2 + s ^ 2) / (2 * s)) =
      2 * ((fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t)) * (m * t + 2 + s ^ 2) /
        (s * lowMeanFractionReal (fiberRayById id).rho_f * m) * u := by
    field_simp [hs.ne',hr.ne',hm.ne']
    ring
  rw [h.2.2.1,hid] at hb
  have hid2 :
      (fiberProfileC (fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f))
        (lowMeanFractionReal (fiberRayById id).d_f) (fiberRayAroot t) +
        (4 * ((fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t)) /
          lowMeanFractionReal (fiberRayById id).rho_f) * u * Real.sqrt (m * t + 2) +
        (lowMeanFractionReal (fiberRayById id).k_f * ((fiberRayAroot t) ^ 2 /
          (1 - fiberRayAroot t)) / lowMeanFractionReal (fiberRayById id).rho_f + fiberRayDelta ra) *
            u ^ 2 * (m * t + 2) - fiberRayDelta ra * u ^ 2 * (m * t + 2) ^ 2) / m =
      fiberProfileC (fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f))
        (lowMeanFractionReal (fiberRayById id).d_f) (fiberRayAroot t) / m +
      (4 * ((fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t)) * u /
        (lowMeanFractionReal (fiberRayById id).rho_f * m)) * Real.sqrt (m * t + 2) +
      (m * t + 2) / m * (lowMeanFractionReal (fiberRayById id).k_f *
        ((fiberRayAroot t) ^ 2 / (1 - fiberRayAroot t)) /
        lowMeanFractionReal (fiberRayById id).rho_f + fiberRayDelta ra - fiberRayDelta ra *
        (m * t + 2)) * u ^ 2 := by ring
  rw [hid2]
  linarith only [hb,hg]

end Erdos993Lean.Analytic.V213
