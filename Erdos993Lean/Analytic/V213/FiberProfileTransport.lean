module

public import Erdos993Lean.Analytic.V213.FiberProfileDefinitions
public import Erdos993Lean.Analytic.V213.FiberRayComparison

/-!
Literal Eq96 actual-deficit transfer, with original q retained.
The common E profile follows the separate reciprocal-square-root,
record-rate, record-kappa and negative variance-bonus comparisons.
No sign of a possibly negative combined loss is assumed.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiber_profile_record_ratios (id : FiberRayIdentity) :
    (63 / 100 : ℝ) ≤ lowMeanFractionReal (fiberRayById id).rho_f ∧
      lowMeanFractionReal (fiberRayById id).k_f / lowMeanFractionReal (fiberRayById id).rho_f ≤
        (17 / 6) / (63 / 100) := by
  cases id <;> norm_num [fiberRayById,lowMeanFractionReal]

theorem fiber_profile_reciprocal_sqrt {N : ℝ} (hN : 25 / 3 ≤ N) :
    1 / Real.sqrt N ≤ 97 / 280 := by
  have hNp : 0 < N := by linarith only [hN]
  have hs := Real.sq_sqrt hNp.le
  have hsp := Real.sqrt_pos.mpr hNp
  have hb : (280 / 97 : ℝ) ≤ Real.sqrt N := by nlinarith only [hN,hs,hsp]
  apply (div_le_iff₀ hsp).2
  linarith only [hb]

theorem fiber_profile_bonus_coefficient {m t ra : ℝ}
    (hm : 19 ≤ m) (ht : 0 < t) (hra : 0 ≤ ra) (hrah : ra ≤ 1 / 2) :
    fiberRayDelta ra * (1 - 2 * (m * t + 2)) ≤ 1 - 2 * (19 * t + 2) := by
  have ho : 0 < 1 - ra ^ 2 := by nlinarith only [hra,hrah]
  have hd : 1 ≤ fiberRayDelta ra := by
    unfold fiberRayDelta
    rw [inv_eq_one_div]
    exact (one_le_div ho).2 (by nlinarith only [sq_nonneg ra])
  have hm0 : 0 < m := by linarith only [hm]
  have hn : 1 - 2 * (m * t + 2) ≤ 0 := by have hp := mul_pos hm0 ht; linarith only [hp]
  have hb := mul_le_mul_of_nonpos_right hd hn
  have hmt := mul_le_mul_of_nonneg_right hm ht.le
  linarith only [hb,hmt]

theorem fiber_profile_ray_E (id : FiberRayIdentity) {m t ra u : ℝ} {g : ℝ → ℝ}
    (hm : 19 ≤ m) (ht : 1 / 3 ≤ t) (ht1 : t < 1)
    (hra : 0 ≤ ra) (hrah : ra ≤ 1 / 2) (hu : 0 ≤ u) (hg : g t ≤ 0) :
    fiberRayE id g m t ra u ≤ fiberProfileE t u (fiberRayAroot t) := by
  have htp : 0 < t := by linarith only [ht]
  have hmp : 0 < m := by linarith only [hm]
  have hN : 25 / 3 ≤ m * t + 2 := by
    have hmt := mul_le_mul hm ht (by norm_num) hmp.le
    norm_num at hmt
    linarith only [hmt]
  have hsqrt := fiber_profile_reciprocal_sqrt hN
  have hs0 : 0 < Real.sqrt (m * t + 2) := Real.sqrt_pos.mpr (by linarith only [hN])
  have hf := fiber_profile_record_ratios id
  have hr := (fiber_ray_record_guards id).2.2.2.2.2.1
  have hG := shared_G_nonneg (5 / 2 * Real.log t)
  have hrf : 1 / lowMeanFractionReal (fiberRayById id).rho_f ≤ 1 / (63 / 100 : ℝ) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hf.1
  have hS := mul_le_mul hrf hsqrt (by positivity) (by positivity)
  have hS' := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 2 * G (5 / 2 * Real.log t) * u)
  have hK := mul_le_mul_of_nonneg_right hf.2 hG
  have hD := fiber_profile_bonus_coefficient hm htp hra hrah
  have hK' := mul_le_mul_of_nonneg_right hK (sq_nonneg u)
  have hD' := mul_le_mul_of_nonneg_right hD (sq_nonneg u)
  have hsum : fiberRayHPrime (fiberRayA id t) (fiberRayK id t) (fiberRayDelta ra) u (m * t + 2) ≤
      97 * G (5 / 2 * Real.log t) / (140 * (63 / 100)) * u +
      ((17 / 6) * G (5 / 2 * Real.log t) / (63 / 100) + 1 - 2 * (19 * t + 2)) * u ^ 2 := by
    unfold fiberRayHPrime fiberRayA fiberRayK
    have hsEq : 2 * G (5 / 2 * Real.log t) * u *
        ((1 / lowMeanFractionReal (fiberRayById id).rho_f) * (1 / Real.sqrt (m * t + 2))) =
        (4 * G (5 / 2 * Real.log t) / lowMeanFractionReal (fiberRayById id).rho_f) * u /
          (2 * Real.sqrt (m * t + 2)) := by ring
    have hsEq' : 2 * G (5 / 2 * Real.log t) * u * ((1 / (63 / 100 : ℝ)) * (97 / 280)) =
        97 * G (5 / 2 * Real.log t) / (140 * (63 / 100)) * u := by ring
    rw [hsEq,hsEq'] at hS'
    have hKEq : (lowMeanFractionReal (fiberRayById id).k_f /
        lowMeanFractionReal (fiberRayById id).rho_f) * G (5 / 2 * Real.log t) * u ^ 2 =
      (lowMeanFractionReal (fiberRayById id).k_f * G (5 / 2 * Real.log t) /
        lowMeanFractionReal (fiberRayById id).rho_f) * u ^ 2 := by ring
    have hKEq' : ((17 / 6 : ℝ) / (63 / 100)) * G (5 / 2 * Real.log t) * u ^ 2 =
      ((17 / 6) * G (5 / 2 * Real.log t) / (63 / 100)) * u ^ 2 := by ring
    rw [hKEq,hKEq'] at hK'
    linarith only [hS',hK',hD']
  have hterm := mul_le_mul_of_nonneg_left hsum htp.le
  have hroot := (fiber_ray_root_formulas htp ht1).2.2.1
  calc
    fiberRayE id g m t ra u ≤ fiberRayF t +
        t * fiberRayHPrime (fiberRayA id t) (fiberRayK id t) (fiberRayDelta ra) u (m * t + 2) := by
      unfold fiberRayE
      linarith only [hg]
    _ ≤ fiberRayF t + t * (97 * G (5 / 2 * Real.log t) / (140 * (63 / 100)) * u +
        ((17 / 6) * G (5 / 2 * Real.log t) / (63 / 100) + 1 - 2 * (19 * t + 2)) * u ^ 2) :=
      add_le_add (le_refl _) hterm
    _ = fiberProfileE t u (fiberRayAroot t) := by
      unfold fiberRayF fiberProfileE fiberProfileF fiberProfileG0
      rw [hroot]
      ring

theorem fiber_profile_deficit_bound (id : FiberRayIdentity) {M : ℕ}
    {q mu m s ra b beta : ℝ} {g : ℝ → ℝ}
    (hMf : lowMeanFractionReal (fiberRayById id).m_f ≤ (M : ℝ))
    (hq0 : 1 / 4 ≤ q) (hqh : q ≤ 3 / 4) (hm : 19 ≤ m) (hmu : m ≤ mu) (hs : 0 < s)
    (hra : 0 ≤ ra) (har : ra ≤ |fiberSkew q|)
    (hrR : |fiberSkew q| ≤ lowMeanFractionReal (fiberRayById id).R)
    (ht0 : 1 / 3 ≤ (M : ℝ) / mu) (hth : (M : ℝ) / mu ≤ 3 / 5)
    (hg : g ((M : ℝ) / mu) ≤ b + beta * ((M : ℝ) / mu - 1))
    (hbar : b + beta * ((M : ℝ) / mu - 1) ≤ 0) :
    fiberDeficit q mu g M ≤ max 0 (max
      (fiberProfileD (fiberRayCF (lowMeanFractionReal (fiberRayById id).m_f))
        (lowMeanFractionReal (fiberRayById id).d_f)
        (lowMeanFractionReal (fiberRayById id).rho_f) (lowMeanFractionReal (fiberRayById id).k_f)
        m s (fiberRayDelta ra) b beta ((M : ℝ) / mu) |fiberSkew q|
        (fiberRayAroot ((M : ℝ) / mu)))
      (fiberProfileE ((M : ℝ) / mu) |fiberSkew q| (fiberRayAroot ((M : ℝ) / mu)))) := by
  have hmu19 := hm.trans hmu
  have hm0 : 0 < m := by linarith only [hm]
  have hmu0 : 0 < mu := hm0.trans_le hmu
  have ht : 0 < (M : ℝ) / mu := by linarith only [ht0]
  have ht1 : (M : ℝ) / mu < 1 := by linarith only [hth]
  have hrh : |fiberSkew q| ≤ 1 / 2 := by
    rw [abs_le]
    unfold fiberSkew
    constructor <;> linarith only [hq0,hqh]
  have hmt : m * ((M : ℝ) / mu) ≤ (M : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right hmu ht.le
    have hid : mu * ((M : ℝ) / mu) = (M : ℝ) := by field_simp [hmu0.ne']
    rwa [hid] at hmul
  have hray := fiber_ray_bound_all_q id hMf hq0 hqh hmu19 hra har hrR ht0 hth
    (hg.trans hbar) hm0 hmt
  have hD := fiber_profile_ray_D (ra := ra) (u := |fiberSkew q|) ht ht1 hm0 hs
    (abs_nonneg (fiberSkew q)) hg id
  have hE := fiber_profile_ray_E id (u := |fiberSkew q|) hm ht0 ht1 hra (har.trans hrh)
    (abs_nonneg (fiberSkew q)) (hg.trans hbar)
  exact hray.trans (max_le_max (le_refl 0) (max_le_max hD hE))

end Erdos993Lean.Analytic.V213
