module

public import Erdos993Lean.Analytic.V213.FiberAffinePolynomialCheck
public import Erdos993Lean.Analytic.V213.FiberAffineDefinitions

/-!
Exact real polynomial semantics for the remaining accepted F03 records.
The source coefficients, errors, square-form metadata and discriminant
are bound before use. All closed w in[0,3/2] and beta in[0,1] are covered;
no positive sample of a polynomial is substituted for its domain proof.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_affine_A_polynomial (w : ℝ) : fiberAffineA w = fiberAffinePolynomialValue .a w := by
  rw [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal,fiberAffineA]
  ring

theorem fiber_affine_V_polynomial (w : ℝ) : fiberAffineV w = fiberAffinePolynomialValue .v w := by
  rw [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal,fiberAffineV]
  ring

theorem fiber_affine_c_polynomial (w : ℝ) : fiberAffineCurvature w = fiberAffinePolynomialValue .c w := by
  rw [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal,fiberAffineCurvature]
  ring

theorem fiber_affine_p_polynomial (w : ℝ) : fiberAffineP w = fiberAffinePolynomialValue .p w := by
  rw [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal,fiberAffineP]
  ring

theorem fiber_affine_q_polynomial (w : ℝ) : fiberAffineQ w = fiberAffinePolynomialValue .q w := by
  rw [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal,fiberAffineQ]
  ring

theorem fiber_affine_polynomial_errors (w : ℝ) :
    fiberAffineA w - fiberAffineP w = fiberAffinePolynomialValue .errorA w ∧
    fiberAffineQ w - (1 - fiberAffineV w) = fiberAffinePolynomialValue .errorQ w := by
  rw [fiber_affine_A_polynomial,fiber_affine_p_polynomial,fiber_affine_q_polynomial,fiber_affine_V_polynomial]
  simp only [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal]
  constructor <;> ring

theorem fiber_affine_error_values (w : ℝ) :
    fiberAffinePolynomialValue .errorA w = 99 * w / 25000 + 14 / 3125 ∧
    fiberAffinePolynomialValue .errorQ w = w ^ 2 / 80 + 1323 * w / 50000 + 43 / 37500 := by
  simp only [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal]
  constructor <;> ring

theorem fiber_affine_polynomial_order {w : ℝ} (hw : 0 ≤ w) :
    fiberAffineP w ≤ fiberAffineA w ∧ 1 - fiberAffineV w ≤ fiberAffineQ w := by
  have h := fiber_affine_polynomial_errors w
  rw [(fiber_affine_error_values w).1,(fiber_affine_error_values w).2] at h
  constructor <;> nlinarith only [h.1,h.2,hw,sq_nonneg w]

theorem fiber_affine_positive_quadratic_identity (w : ℝ) :
    fiberAffinePolynomialValue .positiveQuadratic w =
      lowMeanFractionReal (fiberAffineAuxiliaryById .squareCoefficient).2 *
        (w + lowMeanFractionReal (fiberAffineAuxiliaryById .squareShift).2) ^ 2 +
          lowMeanFractionReal (fiberAffineAuxiliaryById .squareConstant).2 := by
  rw [fiber_affine_polynomial_value,
    (fiber_affine_auxiliary_binding .squareCoefficient).2.2.1,
    (fiber_affine_auxiliary_binding .squareShift).2.2.1,
    (fiber_affine_auxiliary_binding .squareConstant).2.2.1]
  norm_num [fiberAffinePolynomialCanonical,fiberAffineAuxiliaryCanonical,lowMeanFractionReal]
  ring

theorem fiber_affine_positive_quadratic (w : ℝ) : 0 < 12 - 17 * w + (27 / 4 : ℝ) * w ^ 2 := by
  have he := fiber_affine_positive_quadratic_identity w
  rw [fiber_affine_polynomial_value,
    (fiber_affine_auxiliary_binding .squareCoefficient).2.2.1,
    (fiber_affine_auxiliary_binding .squareShift).2.2.1,
    (fiber_affine_auxiliary_binding .squareConstant).2.2.1] at he
  norm_num [fiberAffinePolynomialCanonical,fiberAffineAuxiliaryCanonical,lowMeanFractionReal] at he
  nlinarith only [he,sq_nonneg (w - 34 / 27)]

theorem fiber_affine_discriminant_positive (w : ℝ) :
    0 < (1015 : ℝ) * w ^ 2 - 2941 * w + 2132 := by
  have hd := fiber_affine_discriminant_deficit
  have he : (4 * 1015 : ℝ) * (1015 * w ^ 2 - 2941 * w + 2132) =
      (2 * 1015 * w - 2941) ^ 2 + (4 * 1015 * 2132 - 2941 ^ 2) := by ring
  nlinarith only [hd,he,sq_nonneg (2 * 1015 * w - 2941)]

theorem fiber_affine_C_pos {w : ℝ} (hw : w ≤ 3 / 2) : 0 < fiberAffineC w := by
  unfold fiberAffineC
  linarith only [hw]

theorem fiber_affine_positive_part_bound {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    max (w - 641 / 625) 0 * fiberAffineC w ≤ 7 * w ^ 2 / 64 := by
  have hc := fiber_affine_C_pos hwh
  have he : 7 * w ^ 2 / 64 - (w - 41 / 40) * fiberAffineC w =
      ((1015 : ℝ) * w ^ 2 - 2941 * w + 2132) / 1600 := by
    unfold fiberAffineC
    ring
  have hd := fiber_affine_discriminant_positive w
  have hs : (w - 641 / 625) * fiberAffineC w ≤ (w - 41 / 40) * fiberAffineC w := by
    apply mul_le_mul_of_nonneg_right _ hc.le
    linarith
  by_cases hh : 0 ≤ w - (641 / 625 : ℝ)
  · rw [max_eq_left hh]
    nlinarith only [he,hd,hs]
  · rw [max_eq_right (le_of_lt (lt_of_not_ge hh)),zero_mul]
    positivity

theorem fiber_affine_curvature_bounds {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    207 / 32 ≤ fiberAffineCurvature w ∧ fiberAffineCurvature w ≤ 9 := by
  unfold fiberAffineCurvature
  constructor <;> nlinarith only [hw0,hwh,sq_nonneg w]

theorem fiber_affine_V_increases : StrictMonoOn fiberAffineV (Icc 0 (3 / 2 : ℝ)) := by
  intro x hx y hy hxy
  have he : fiberAffineV y - fiberAffineV x =
      (y - x) * (201323 / 50000 - (63 / 80 : ℝ) * (x + y)) := by
    unfold fiberAffineV
    ring
  have hb : 0 < (201323 / 50000 : ℝ) - (63 / 80 : ℝ) * (x + y) := by
    linarith only [hx.2,hy.2]
  have hp := mul_pos (sub_pos.mpr hxy) hb
  linarith only [he,hp]

theorem fiber_affine_V_upper {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    fiberAffineV w < 5 / 8 := by
  have he : fiberAffineV (3 / 2) = (120459 / 200000 : ℝ) := by
    rw [fiber_affine_V_polynomial,fiber_affine_polynomial_value]
    norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal]
  have hm := fiber_affine_V_increases.monotoneOn ⟨hw0,hwh⟩ (by norm_num) hwh
  rw [he] at hm
  exact hm.trans_lt fiber_affine_V_endpoint_upper

theorem fiber_affine_V_square {w beta : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2)
    (hb0 : 0 ≤ beta) (hbh : beta ≤ 1) :
    (fiberAffineV w - beta) ^ 2 ≤ (1 - fiberAffineV w) ^ 2 + 1 / 4 := by
  have hv := (fiber_affine_V_upper hw0 hwh).le
  have hp := mul_nonneg (by linarith only [hbh] : 0 ≤ 1 - beta)
    (by linarith only [hv] : 0 ≤ 5 / 4 - 2 * fiberAffineV w)
  have hb := mul_nonneg hb0 (by linarith only [hbh] : 0 ≤ 5 / 4 - beta)
  nlinarith only [hp,hb]

theorem fiber_affine_quartic_identity (w : ℝ) :
    2 * fiberAffineCurvature w * fiberAffineP w - fiberAffineQ w ^ 2 =
      fiberAffinePolynomialValue .quarticLeft w ∧
    fiberAffinePolynomialValue .quarticRight w =
      203 / 225 + w * (12 - 17 * w + 27 * w ^ 2 / 4) + 37 * w / 75 +
        89 * w ^ 2 / 600 + 37 * w ^ 3 / 1600 + 1457 * w ^ 3 * (3 / 2 - w) / 800 := by
  rw [fiber_affine_c_polynomial,fiber_affine_p_polynomial,fiber_affine_q_polynomial]
  simp only [fiber_affine_polynomial_value]
  norm_num [fiberAffinePolynomialCanonical,lowMeanFractionReal]
  constructor <;> ring

theorem fiber_affine_quartic_lower {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    203 / 225 ≤ 2 * fiberAffineCurvature w * fiberAffineP w - fiberAffineQ w ^ 2 := by
  have he := fiber_affine_quartic_identity w
  have hv : fiberAffinePolynomialValue .quarticLeft w = fiberAffinePolynomialValue .quarticRight w := by
    simp only [fiber_affine_polynomial_value,fiberAffinePolynomialCanonical]
  have hp := mul_nonneg hw0 (fiber_affine_positive_quadratic w).le
  have h3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
  have hlast : 0 ≤ w ^ 3 * (3 / 2 - w) := mul_nonneg h3 (by linarith only [hwh])
  nlinarith only [he.1,he.2,hv,hp,hw0,sq_nonneg w,h3,hlast]

theorem fiber_affine_tangent_discriminant {w beta : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2)
    (hb0 : 0 ≤ beta) (hbh : beta ≤ 1) :
    587 / 900 ≤ 2 * fiberAffineCurvature w * fiberAffineA w - (fiberAffineV w - beta) ^ 2 := by
  have hc := (fiber_affine_curvature_bounds hw0 hwh).1
  have hord := fiber_affine_polynomial_order hw0
  have hA := mul_le_mul_of_nonneg_left hord.1 (by linarith only [hc] : 0 ≤ 2 * fiberAffineCurvature w)
  have hv := fiber_affine_V_upper hw0 hwh
  have hq := sq_le_sq₀ (by linarith only [hv] : 0 ≤ 1 - fiberAffineV w)
    (by linarith only [hv,hord.2] : 0 ≤ fiberAffineQ w)
  have hs := hq.2 hord.2
  have hV := fiber_affine_V_square hw0 hwh hb0 hbh
  have hquartic := fiber_affine_quartic_lower hw0 hwh
  nlinarith only [hA,hs,hV,hquartic]

end Erdos993Lean.Analytic.V213
