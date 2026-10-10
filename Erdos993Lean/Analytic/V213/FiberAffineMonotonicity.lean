module

public import Erdos993Lean.Analytic.V213.FiberAffineDefinitions

/-!
Analytic xi monotonicity of the actual Y in Theorem6.15 on the entire
closed domain N>=22, w in[0,3/2], xi in[4/25,1/sqrt(3)]. The proof concerns
the minorant and gives its printed positive derivative-sign margin.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

theorem fiber_sqrt_ratio_antitone {B N : ℝ} (hB : 1 ≤ B) (hBN : B ≤ N) :
    Real.sqrt N / (N + 1) ≤ Real.sqrt B / (B + 1) := by
  have hb : 0 < B := by linarith
  have hn : 0 < N := hb.trans_le hBN
  have hb1 : 0 < B + 1 := by linarith
  have hn1 : 0 < N + 1 := by linarith
  apply (div_le_div_iff₀ hn1 hb1).2
  apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt N * (B + 1))
    (by positivity : 0 ≤ Real.sqrt B * (N + 1))).1
  rw [mul_pow, mul_pow, Real.sq_sqrt hn.le, Real.sq_sqrt hb.le]
  have hp : 0 ≤ (N - B) * (B * N - 1) :=
    mul_nonneg (sub_nonneg.mpr hBN) (by nlinarith only [hB, hBN])
  nlinarith only [hp]

theorem fiber_affine_H_lower {N : ℝ} (hN : 22 ≤ N) : 21 ≤ fiberAffineH N := by
  have hn : 0 < N := by linarith
  unfold fiberAffineH
  have hi := one_div_pos.mpr hn
  linarith only [hN, hi]

theorem fiber_affine_k_bounds {w : ℝ} (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) :
    0 ≤ fiberAffineK w ∧ fiberAffineK w ≤ Real.sqrt 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hs6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hsp : 0 < Real.sqrt (3 / 2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have he : Real.sqrt (6 : ℝ) * Real.sqrt (3 / 2 : ℝ) = 3 := by
    apply (sq_eq_sq₀ (by positivity) (by norm_num : (0 : ℝ) ≤ 3)).1
    rw [mul_pow, hs6, hs]
    norm_num
  unfold fiberAffineK
  constructor
  · positivity
  · apply (div_le_iff₀ hsp).2
    rw [he]
    linarith only [hwh]

theorem fiber_affine_derivative_factor {N w xi : ℝ} (hN : 22 ≤ N)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hxi0 : 0 ≤ xi) (hxih : xi ^ 2 ≤ 1 / 3) :
    0 ≤ (4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1) ∧
      (4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1) ≤ 5 / 8 := by
  have hn : 0 < N := by linarith
  have hm : 0 < N + 1 := by linarith
  have hk := fiber_affine_k_bounds hw0 hwh
  have hxi : xi ≤ 3 / 5 := by nlinarith only [hxih, hxi0]
  have hr := fiber_sqrt_ratio_antitone (by norm_num : (1 : ℝ) ≤ 22) hN
  have hs22 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 22)
  have hs6 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)
  have hsprod : Real.sqrt (6 : ℝ) * Real.sqrt (22 : ℝ) ≤ 23 / 2 := by
    apply (sq_le_sq₀ (by positivity : 0 ≤ Real.sqrt (6 : ℝ) * Real.sqrt 22)
      (by norm_num : (0 : ℝ) ≤ 23 / 2)).1
    rw [mul_pow, hs6, hs22]
    norm_num
  have hroot : fiberAffineK w * Real.sqrt N / (N + 1) ≤ 1 / 2 := by
    calc
      _ ≤ Real.sqrt 6 * (Real.sqrt N / (N + 1)) := by
        convert mul_le_mul_of_nonneg_right hk.2 (by positivity : 0 ≤ Real.sqrt N / (N + 1)) using 1 <;> ring
      _ ≤ Real.sqrt 6 * (Real.sqrt 22 / 23) :=
        mul_le_mul_of_nonneg_left (by norm_num only at hr; exact hr) (Real.sqrt_nonneg _)
      _ ≤ 1 / 2 := by
        rw [show Real.sqrt 6 * (Real.sqrt 22 / 23) = (Real.sqrt 6 * Real.sqrt 22) / 23 by ring]
        apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 23)).2
        convert hsprod using 1 <;> ring
  have hx : 4 * xi / (N + 1) ≤ (12 / 115 : ℝ) := by
    apply (div_le_iff₀ hm).2
    linarith only [hxi, hN]
  constructor
  · exact div_nonneg (add_nonneg (by positivity) (mul_nonneg hk.1 (Real.sqrt_nonneg _))) hm.le
  · have he : (4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1) =
        4 * xi / (N + 1) + fiberAffineK w * Real.sqrt N / (N + 1) := by ring
    rw [he]
    linarith only [hx, hroot]

theorem fiber_affine_Y_derivative_sign {N w xi : ℝ} (hN : 22 ≤ N)
    (hw0 : 0 ≤ w) (hwh : w ≤ 3 / 2) (hxil : 4 / 25 ≤ xi) (hxih : xi ^ 2 ≤ 1 / 3) :
    7 / 100 ≤ 2 * xi - (xi ^ 2 + (1 - w) / fiberAffineH N) *
      ((4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1)) := by
  have hh := fiber_affine_H_lower hN
  have hh0 : 0 < fiberAffineH N := by linarith
  have hx0 : 0 ≤ xi := by linarith
  have ht := fiber_affine_derivative_factor hN hw0 hwh hx0 hxih
  have hp : xi ^ 2 + (1 - w) / fiberAffineH N ≤ 2 / 5 := by
    have he : (1 - w) / fiberAffineH N ≤ (1 / 21 : ℝ) := by
      apply (div_le_iff₀ hh0).2
      linarith only [hh, hw0]
    linarith only [he, hxih]
  by_cases hpar : 0 ≤ xi ^ 2 + (1 - w) / fiberAffineH N
  · have hm := mul_le_mul hp ht.2 ht.1 (by norm_num : (0 : ℝ) ≤ 2 / 5)
    nlinarith only [hxil, hm]
  · have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hpar)) ht.1
    linarith only [hxil, hn]

theorem fiber_hasDerivAt_affine_Y {N : ℝ} (hN : 22 ≤ N) (w xi : ℝ) :
    HasDerivAt (fiberAffineY N w)
      (fiberAffineH N * Real.exp (-(2 * xi ^ 2 + fiberAffineK w * Real.sqrt N * xi) / (N + 1)) *
        (2 * xi - (xi ^ 2 + (1 - w) / fiberAffineH N) *
          ((4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1)))) xi := by
  have hh : fiberAffineH N ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 21) (fiber_affine_H_lower hN))
  have he : HasDerivAt (fun x : ℝ => -(2 * x ^ 2 + fiberAffineK w * Real.sqrt N * x) / (N + 1))
      (-(4 * xi + fiberAffineK w * Real.sqrt N) / (N + 1)) xi := by
    convert ((((hasDerivAt_id xi).pow 2).const_mul 2).add
      ((hasDerivAt_id xi).const_mul (fiberAffineK w * Real.sqrt N))).neg.div_const (N + 1) using 1
    · funext x
      rfl
    · dsimp
      ring
  have ha : HasDerivAt (fun x : ℝ => 1 - w + fiberAffineH N * x ^ 2)
      (2 * fiberAffineH N * xi) xi := by
    convert (((hasDerivAt_id xi).pow 2).const_mul (fiberAffineH N)).const_add (1 - w) using 1
    · funext x
      rfl
    · dsimp
      ring
  convert ha.mul he.exp using 1
  · rfl
  · field_simp [hh]
    ring

end Erdos993Lean.Analytic.V213
