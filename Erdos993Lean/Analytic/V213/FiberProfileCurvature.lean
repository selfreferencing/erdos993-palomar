module

public import Erdos993Lean.Analytic.V213.FiberProfileLineCalculus

/-!
Literal second-derivative bounds on a root-line piece. The hypotheses
are the printed scalar guards; later named profile consumers discharge
them from the accepted data.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

theorem fiber_profile_reciprocal_gain {beta d0 w B A : ℝ}
    (hb : 0 < beta) (hd : 0 ≤ d0) (hw : 0 < w) (hB : 2 ≤ B)
    (hA : B * d0 / beta ≤ A) :
    4 * beta * d0 / w ^ 3 ≤ 2 * beta ^ 2 * A / w ^ 3 := by
  have hBd : 2 * d0 ≤ B * d0 := mul_le_mul_of_nonneg_right hB hd
  have hA' := (div_le_iff₀ hb).mp hA
  have hp := mul_le_mul_of_nonneg_left (hBd.trans hA') (by positivity : 0 ≤ 2 * beta)
  apply (div_le_div_iff_of_pos_right (pow_pos hw 3)).2
  nlinarith only [hp]

theorem fiber_profile_negative_reciprocal {beta cf m w : ℝ}
    (hb0 : 0 ≤ beta) (hb : beta ≤ 4 / 3) (hc0 : 0 ≤ cf) (hc : cf ≤ 12 / 5)
    (hm : 19 ≤ m) (hw : 0 < w) :
    2 * beta ^ 2 * cf / (m * (1 + w) ^ 3) < 1 / 2 := by
  have hbs : beta ^ 2 ≤ (16 / 9 : ℝ) := by nlinarith only [hb0,hb]
  have hp := mul_le_mul_of_nonneg_right hbs hc0
  have hp' := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 16 / 9)
  have hnum : 2 * beta ^ 2 * cf ≤ (128 / 15 : ℝ) := by nlinarith only [hp,hp']
  have hw3 : 1 ≤ (1 + w) ^ 3 := one_le_pow₀ (by linarith only [hw])
  have hden : 19 ≤ m * (1 + w) ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hw3 (by linarith only [hm] : 0 ≤ m)
    linarith only [h,hm]
  apply (div_lt_iff₀ (by linarith only [hden] : 0 < m * (1 + w) ^ 3)).2
  linarith only [hnum,hden]

theorem fiber_profile_D_second_strict {cf df rho kappa m s delta alpha beta t u R : ℝ}
    (hr : 0 < rho) (hk : 0 ≤ kappa) (hm : 19 ≤ m) (hs : 0 < s)
    (hcf0 : 0 ≤ cf) (hcf : cf ≤ 12 / 5) (hc : 0 ≤ cf + df - 11 / 10)
    (hd : 0 ≤ delta) (hu : 0 ≤ u) (huR : u ≤ R)
    (hloss : delta * m * R ^ 2 ≤ 7 / 2)
    (ha : 1 < alpha) (hb : 1 ≤ beta) (hbhi : beta ≤ 4 / 3)
    (hw : 0 < beta * t - (alpha - 1))
    (hcurve : 15 < 4 * beta * (alpha - 1) / (beta * t - (alpha - 1)) ^ 3) :
    5 / 2 < fiberProfileLineSecond (fiberProfileDP2 rho kappa m s delta beta u)
      (fiberProfileDK cf df rho kappa m s alpha beta u) (cf / m) beta (alpha - 1) t := by
  have hm0 : 0 < m := by linarith only [hm]
  have hb0 : 0 < beta := by linarith only [hb]
  have hB := fiber_profile_B_lower hr hk hm0 hs hu
  have hA : fiberProfileB1 rho kappa s u * (alpha - 1) / beta ≤
      fiberProfileB0 rho kappa m s u + fiberProfileB1 rho kappa s u * (alpha - 1) / beta +
        (cf + df - 11 / 10) / m := by
    have hlast := div_nonneg hc hm0.le
    linarith only [hB.2,hlast]
  have hrec := fiber_profile_reciprocal_gain hb0 (by linarith only [ha]) hw hB.1 hA
  have hneg := fiber_profile_negative_reciprocal hb0.le hbhi hcf0 hcf hm hw
  have hsq : u ^ 2 ≤ R ^ 2 := by nlinarith only [hu,huR]
  have hls := mul_le_mul_of_nonneg_left hsq (mul_nonneg hd hm0.le)
  have hbase : 4 ≤ 2 * beta * fiberProfileB1 rho kappa s u := by
    have hp := mul_le_mul_of_nonneg_left hB.1 hb0.le
    nlinarith only [hp,hb]
  rw [fiber_profile_D_second_identity hm0.ne']
  have hid : 2 * beta ^ 2 * ((fiberProfileB0 rho kappa m s u +
      fiberProfileB1 rho kappa s u * (alpha - 1) / beta + (cf + df - 11 / 10) / m) /
        (beta * t - (alpha - 1)) ^ 3 - cf / (m * (1 + beta * t - (alpha - 1)) ^ 3)) =
      2 * beta ^ 2 * (fiberProfileB0 rho kappa m s u +
        fiberProfileB1 rho kappa s u * (alpha - 1) / beta + (cf + df - 11 / 10) / m) /
          (beta * t - (alpha - 1)) ^ 3 -
        2 * beta ^ 2 * cf / (m * (1 + (beta * t - (alpha - 1))) ^ 3) := by ring
  rw [hid]
  nlinarith only [hbase,hrec,hcurve,hneg,hls,hloss]

theorem fiber_profile_E_second_strict {alpha beta t u : ℝ}
    (ha : 1 < alpha) (hb : 1 ≤ beta) (hu : 0 ≤ u) (huhi : u ≤ 7 / 25)
    (hw : 0 < beta * t - (alpha - 1))
    (hcurve : 15 < 4 * beta * (alpha - 1) / (beta * t - (alpha - 1)) ^ 3) :
    4 < fiberProfileLineSecond (beta * fiberProfileEB0 u - 9 / 2 - 38 * u ^ 2)
      ((alpha - 1) * fiberProfileEB0 u / beta) 0 beta (alpha - 1) t := by
  have hb0 : 0 < beta := by linarith only [hb]
  have hB := fiber_profile_EB_lower hu
  have hrec := fiber_profile_reciprocal_gain (d0 := alpha - 1)
    hb0 (by linarith only [ha]) hw hB (le_refl _)
  have hid : 2 * beta ^ 2 * (fiberProfileEB0 u * (alpha - 1) / beta) /
      (beta * t - (alpha - 1)) ^ 3 =
      2 * beta * (alpha - 1) * fiberProfileEB0 u / (beta * t - (alpha - 1)) ^ 3 := by
    field_simp [hb0.ne'] <;> ring
  rw [hid] at hrec
  have hp := mul_le_mul_of_nonneg_left hB hb0.le
  have hbase : 4 ≤ 2 * beta * fiberProfileEB0 u := by nlinarith only [hp,hb]
  have hsq : u ^ 2 ≤ (49 / 625 : ℝ) := by nlinarith only [hu,huhi]
  rw [fiber_profile_E_second_identity _ _ _ _ hb0.ne']
  nlinarith only [hbase,hrec,hcurve,hsq]

end Erdos993Lean.Analytic.V213
