module

public import Erdos993Lean.Analytic.V213.FiberAffinePolynomialBounds
public import Erdos993Lean.Analytic.V213.FiberLowerCurvature

/-!
Literal affine H_beta calculus and whole-domain curvature for t>=3/4.
The negative term is controlled by the accepted F03 positive-part bound,
the actual half-integer power and the checked sqrt3/rational comparisons.
The resulting c(w) lower bound includes both closed t/w endpoints.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberAffineSupportPrime (beta t w : ℝ) : ℝ :=
  9 * (t - 1) + (w - 1) - beta + fiberAffineC w *
    (-(3 / 2 : ℝ) * (641 / 625 - w) * t ^ (-(5 / 2 : ℝ)) -
      (64 / 125 : ℝ) * t ^ (-(3 / 2 : ℝ)))

noncomputable def fiberAffineSupportSecond (t w : ℝ) : ℝ :=
  9 + fiberAffineC w * ((15 / 4 : ℝ) * (641 / 625 - w) * t ^ (-(7 / 2 : ℝ)) +
    (96 / 125 : ℝ) * t ^ (-(5 / 2 : ℝ)))

theorem fiber_hasDerivAt_affine_support {beta t w : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => fiberAffineSupport beta x w) (fiberAffineSupportPrime beta t w) t := by
  have h3 := Real.hasDerivAt_rpow_const (x := t) (p := -(3 / 2 : ℝ)) (Or.inl ht.ne')
  have h1 := Real.hasDerivAt_rpow_const (x := t) (p := -(1 / 2 : ℝ)) (Or.inl ht.ne')
  have hTail := ((h3.const_mul (641 / 625 - w)).add (h1.const_mul (128 / 125 : ℝ))).const_mul (fiberAffineC w)
  have h := ((((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (9 / 2 : ℝ)).add
    ((hasDerivAt_id t).const_mul (w - 1))).sub_const (2 / 5 : ℝ)).sub
      (((hasDerivAt_id t).sub_const 1).const_mul beta) |>.add
        hTail
  convert h using 1
  · funext x
    dsimp [fiberAffineSupport]
    ring
  · dsimp [fiberAffineSupportPrime]
    norm_num
    ring

theorem fiber_hasDerivAt_affine_supportPrime {beta t w : ℝ} (ht : 0 < t) :
    HasDerivAt (fun x => fiberAffineSupportPrime beta x w) (fiberAffineSupportSecond t w) t := by
  have h5 := Real.hasDerivAt_rpow_const (x := t) (p := -(5 / 2 : ℝ)) (Or.inl ht.ne')
  have h3 := Real.hasDerivAt_rpow_const (x := t) (p := -(3 / 2 : ℝ)) (Or.inl ht.ne')
  have hTail := ((h5.const_mul (-(3 / 2 : ℝ) * (641 / 625 - w))).sub
    (h3.const_mul (64 / 125 : ℝ))).const_mul (fiberAffineC w)
  have h := (((((hasDerivAt_id t).sub_const 1).const_mul 9).add_const (w - 1)).sub_const beta).add
    hTail
  convert h using 1
  · funext x
    dsimp [fiberAffineSupportPrime]
  · dsimp [fiberAffineSupportSecond]
    norm_num <;> first | (left; ring) | ring

theorem fiber_affine_second_formula {t w : ℝ} (ht : 0 < t) :
    fiberAffineSupportSecond t w = 9 + (3 / 4 : ℝ) * fiberAffineC w * t ^ (-(7 / 2 : ℝ)) *
      (5 * (641 / 625 - w) + (128 / 125 : ℝ) * t) := by
  have hp : t ^ (-(5 / 2 : ℝ)) = t ^ (-(7 / 2 : ℝ)) * t := by
    rw [show -(5 / 2 : ℝ) = -(7 / 2 : ℝ) + 1 by norm_num,Real.rpow_add ht,Real.rpow_one]
  unfold fiberAffineSupportSecond
  rw [hp]
  ring

theorem fiber_affine_sqrt3_lower : (45 / 26 : ℝ) ≤ Real.sqrt 3 := by
  apply (sq_le_sq₀ (by norm_num : (0 : ℝ) ≤ 45 / 26) (Real.sqrt_nonneg _)).1
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  exact fiber_affine_sqrt3_squared

theorem fiber_affine_inverse_seven_halves {t : ℝ} (ht : 3 / 4 ≤ t) :
    t ^ (-(7 / 2 : ℝ)) ≤ 3328 / 1215 := by
  have ht0 : 0 < t := by linarith only [ht]
  have hp := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 3 / 4) ht
    (by norm_num : -(7 / 2 : ℝ) ≤ 0)
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hroot : Real.sqrt (3 / 4 : ℝ) = Real.sqrt 3 / 2 := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity : 0 ≤ Real.sqrt (3 : ℝ) / 2)).1
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 4),div_pow,hsq]
    norm_num
  have hpow : Real.sqrt (3 : ℝ) ^ 7 = 27 * Real.sqrt 3 := by
    calc
      _ = (Real.sqrt (3 : ℝ) ^ 2) ^ 3 * Real.sqrt 3 := by ring
      _ = _ := by rw [hsq]; norm_num
  have he : (3 / 4 : ℝ) ^ (-(7 / 2 : ℝ)) = 128 / (27 * Real.sqrt 3) := by
    have hhalf := fiber_lower_rpow_half_nat (by norm_num : (0 : ℝ) < 3 / 4) 7
    norm_num only [Nat.cast_ofNat] at hhalf
    rw [hhalf,hroot,div_pow,hpow]
    field_simp
    norm_num
  rw [he] at hp
  have hbound : (128 : ℝ) / (27 * Real.sqrt 3) ≤ 3328 / 1215 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 27) hs)).2
    linarith only [fiber_affine_sqrt3_lower]
  exact hp.trans hbound

theorem fiber_affine_support_curvature {t w : ℝ} (ht : 3 / 4 ≤ t)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    fiberAffineCurvature w ≤ fiberAffineSupportSecond t w := by
  have ht0 : 0 < t := by linarith only [ht]
  have hc := fiber_affine_C_pos hwh
  have hmax := fiber_affine_positive_part_bound hw0 hwh
  have hle : (w - 641 / 625) * fiberAffineC w ≤ 7 * w ^ 2 / 64 :=
    (mul_le_mul_of_nonneg_right (le_max_left _ _) hc.le).trans hmax
  have hbrace : -(35 / 64 : ℝ) * w ^ 2 ≤
      fiberAffineC w * (5 * (641 / 625 - w) + (128 / 125 : ℝ) * t) := by
    have hp : 0 ≤ fiberAffineC w * ((128 / 125 : ℝ) * t) := by positivity
    nlinarith only [hle,hp]
  have hpow0 : 0 ≤ t ^ (-(7 / 2 : ℝ)) := Real.rpow_nonneg ht0.le _
  have hmul := mul_le_mul_of_nonneg_left hbrace (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) hpow0)
  have he := fiber_affine_second_formula (w := w) ht0
  have hp := fiber_affine_inverse_seven_halves ht
  have hprod := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (105 / 256 : ℝ) * w ^ 2)
  have hrat := mul_le_mul_of_nonneg_right fiber_affine_curvature_ratio.le (sq_nonneg w)
  unfold fiberAffineCurvature
  nlinarith only [hmul,he,hprod,hrat]

theorem fiber_affine_support_at_one (beta w : ℝ) :
    fiberAffineSupport beta 1 w = fiberAffineA w ∧
    fiberAffineSupportPrime beta 1 w = fiberAffineV w - beta := by
  rw [fiber_affine_A_polynomial,fiber_affine_V_polynomial]
  simp only [fiber_affine_polynomial_value]
  norm_num [fiberAffineSupport,fiberAffineSupportPrime,fiberAffineC,
    fiberAffinePolynomialCanonical,lowMeanFractionReal]
  constructor <;> ring

end Erdos993Lean.Analytic.V213
