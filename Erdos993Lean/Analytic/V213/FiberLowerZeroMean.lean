module

public import Erdos993Lean.Analytic.V213.FiberLowerQuadratic

/-!
The literal zero-reciprocal-mean quadratic Q_0 is nonnegative
for every size ratio t>=3/5 and every a in[0,1]. The intermediate range is
proved by an exact square-root polynomial identity, equivalent to Eq83.
No finite transcription family is consumed.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

noncomputable def fiberLowerZeroPolynomial (u : ℝ) : ℝ :=
  9 * u ^ 3 * (u + 1) ^ 2 - (u ^ 4 + u ^ 3 + u ^ 2 + u + 1) ^ 2

theorem fiber_lower_zero_polynomial_lower {u : ℝ} (hu0 : 1 ≤ u) (huh : u ≤ 4 / 3) :
    (37634 / 6561 : ℝ) ≤ fiberLowerZeroPolynomial u := by
  let x : ℝ := u - 1
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hxh : x ≤ (1 / 3 : ℝ) := by dsimp [x]; linarith
  have h3 := pow_le_pow_left₀ hx0 hxh 3
  have h4 := pow_le_pow_left₀ hx0 hxh 4
  have h5 := pow_le_pow_left₀ hx0 hxh 5
  have h6 := pow_le_pow_left₀ hx0 hxh 6
  have h7 := pow_le_pow_left₀ hx0 hxh 7
  have h8 := pow_le_pow_left₀ hx0 hxh 8
  have he : fiberLowerZeroPolynomial u = 11 + 44 * x + 25 * x ^ 2 -
      79 * x ^ 3 - 147 * x ^ 4 - 111 * x ^ 5 - 45 * x ^ 6 - 10 * x ^ 7 - x ^ 8 := by
    dsimp [fiberLowerZeroPolynomial, x]
    ring
  rw [he]
  norm_num at h3 h4 h5 h6 h7 h8
  nlinarith [sq_nonneg x]

theorem fiber_lower_Q_zero_square {t a : ℝ} (ht : 0 < t) :
    2 * Real.sqrt t ^ 3 * fiberLowerQ 0 a t =
      (a - (Real.sqrt t ^ 5 - 1)) ^ 2 +
        (Real.sqrt t - 1) ^ 2 * fiberLowerZeroPolynomial (Real.sqrt t) := by
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs := Real.sq_sqrt ht.le
  rw [fiber_lower_Q_root ht]
  rw [← hs]
  simp only [Real.sqrt_sq hs0.le]
  unfold fiberLowerZeroPolynomial
  field_simp [hs0.ne'] <;> ring

theorem fiber_lower_Q_zero_nonneg {t a : ℝ} (ht : 3 / 5 ≤ t)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) : 0 ≤ fiberLowerQ 0 a t := by
  have ht0 : 0 < t := by linarith
  by_cases ht1 : t ≤ 1
  · have hp := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht0 ht1
      (by norm_num : -(3 / 2 : ℝ) ≤ 0)
    have hterm : 0 ≤ a * (-t + t ^ (-(3 / 2 : ℝ))) := mul_nonneg ha0 (by linarith)
    have hs := mul_nonneg (div_nonneg (sq_nonneg a) (by norm_num : (0 : ℝ) ≤ 2))
      (Real.rpow_nonneg ht0.le (-(3 / 2 : ℝ)))
    unfold fiberLowerQ
    norm_num
    nlinarith [sq_nonneg (t - 1)]
  by_cases htbig : 5 / 3 ≤ t
  · have hpsi : fiberPsi t ≤ -(1 / 3 : ℝ) := by
      unfold fiberPsi
      nlinarith [sq_nonneg (t - 5 / 3)]
    have hterm : 0 ≤ (1 - a) * t := mul_nonneg (by linarith) ht0.le
    have hlast : 0 ≤ a * (1 + a / 2) * t ^ (-(3 / 2 : ℝ)) := by positivity
    have hid : fiberLowerQ 0 a t = -fiberPsi t + (1 - a) * t +
        a * (1 + a / 2) * t ^ (-(3 / 2 : ℝ)) := by
      unfold fiberLowerQ fiberPsi
      ring
    rw [hid]
    linarith
  have hs0 : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hs1 : 1 ≤ Real.sqrt t :=
    (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) ht0.le).2 (by linarith)
  have hs4 : Real.sqrt t ≤ (4 / 3 : ℝ) := (Real.sqrt_le_iff).2 ⟨by norm_num, by linarith⟩
  have hp := fiber_lower_zero_polynomial_lower hs1 hs4
  have hpol : 0 ≤ fiberLowerZeroPolynomial (Real.sqrt t) := by linarith
  have hprod : 0 ≤ (Real.sqrt t - 1) ^ 2 * fiberLowerZeroPolynomial (Real.sqrt t) :=
    mul_nonneg (sq_nonneg _) hpol
  have he := fiber_lower_Q_zero_square (a := a) ht0
  have hwhole : 0 ≤ 2 * Real.sqrt t ^ 3 * fiberLowerQ 0 a t := by
    rw [he]
    exact add_nonneg (sq_nonneg _) hprod
  exact nonneg_of_mul_nonneg_right hwhole (by positivity : 0 < 2 * Real.sqrt t ^ 3)

end Erdos993Lean.Analytic.V213
