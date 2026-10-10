module

public import Erdos993Lean.Analytic.V213.FiberDefinitions
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Convex.Deriv

/-!
Literal Eq83, its derivatives and concavity in the reciprocal
mean. Real powers use their actual positive size-ratio argument. The square-
root form is proved equivalent and is used only for exact algebra.
No generated family is consumed in this module.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real Set

noncomputable def fiberLowerQ (z a t : ℝ) : ℝ :=
  9 / 2 * (t - 1) ^ 2 + 2 * z +
    a * (-t - 2 * z + t ^ (-(3 / 2 : ℝ)) - 3 * z * t ^ (-(5 / 2 : ℝ)) -
      10 * z ^ 2 * t ^ (-(7 / 2 : ℝ))) +
    a ^ 2 / 2 * (t ^ (-(3 / 2 : ℝ)) + 2 * z * t ^ (-(5 / 2 : ℝ)))

noncomputable def fiberLowerQPrime (z a t : ℝ) : ℝ :=
  9 * (t - 1) +
    a * (-1 - 3 / 2 * t ^ (-(5 / 2 : ℝ)) + 15 / 2 * z * t ^ (-(7 / 2 : ℝ)) +
      35 * z ^ 2 * t ^ (-(9 / 2 : ℝ))) +
    a ^ 2 / 2 * (-3 / 2 * t ^ (-(5 / 2 : ℝ)) - 5 * z * t ^ (-(7 / 2 : ℝ)))

noncomputable def fiberLowerQSecond (z a t : ℝ) : ℝ :=
  9 + a * (15 / 4 * t ^ (-(7 / 2 : ℝ)) - 105 / 4 * z * t ^ (-(9 / 2 : ℝ)) -
    315 / 2 * z ^ 2 * t ^ (-(11 / 2 : ℝ))) +
    a ^ 2 / 2 * (15 / 4 * t ^ (-(7 / 2 : ℝ)) + 35 / 2 * z * t ^ (-(9 / 2 : ℝ)))

theorem fiber_lower_rpow_half_nat {t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ (-((n : ℝ) / 2)) = 1 / Real.sqrt t ^ n := by
  rw [show -((n : ℝ) / 2) = (-(n : ℝ)) / 2 by ring,
    Real.rpow_div_two_eq_sqrt _ ht.le, Real.rpow_neg (Real.sqrt_nonneg _),
    Real.rpow_natCast, one_div]

theorem fiber_lower_Q_root {z a t : ℝ} (ht : 0 < t) :
    fiberLowerQ z a t = 9 / 2 * (t - 1) ^ 2 + 2 * z +
      a * (-t - 2 * z + 1 / Real.sqrt t ^ 3 - 3 * z / Real.sqrt t ^ 5 -
        10 * z ^ 2 / Real.sqrt t ^ 7) +
      a ^ 2 / 2 * (1 / Real.sqrt t ^ 3 + 2 * z / Real.sqrt t ^ 5) := by
  unfold fiberLowerQ
  have h3 := fiber_lower_rpow_half_nat ht 3
  have h5 := fiber_lower_rpow_half_nat ht 5
  have h7 := fiber_lower_rpow_half_nat ht 7
  norm_num only [Nat.cast_ofNat] at h3 h5 h7
  rw [h3, h5, h7]
  ring

theorem fiber_lower_QPrime_root {z a t : ℝ} (ht : 0 < t) :
    fiberLowerQPrime z a t = 9 * (t - 1) +
      a * (-1 - 3 / (2 * Real.sqrt t ^ 5) + 15 * z / (2 * Real.sqrt t ^ 7) +
        35 * z ^ 2 / Real.sqrt t ^ 9) +
      a ^ 2 / 2 * (-3 / (2 * Real.sqrt t ^ 5) - 5 * z / Real.sqrt t ^ 7) := by
  unfold fiberLowerQPrime
  have h5 := fiber_lower_rpow_half_nat ht 5
  have h7 := fiber_lower_rpow_half_nat ht 7
  have h9 := fiber_lower_rpow_half_nat ht 9
  norm_num only [Nat.cast_ofNat] at h5 h7 h9
  rw [h5, h7, h9]
  ring

theorem fiber_hasDerivAt_lower_Q {z a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberLowerQ z a) (fiberLowerQPrime z a t) t := by
  have h3 := Real.hasDerivAt_rpow_const (x := t) (p := -(3 / 2 : ℝ)) (Or.inl ht.ne')
  have h5 := Real.hasDerivAt_rpow_const (x := t) (p := -(5 / 2 : ℝ)) (Or.inl ht.ne')
  have h7 := Real.hasDerivAt_rpow_const (x := t) (p := -(7 / 2 : ℝ)) (Or.inl ht.ne')
  have h := (((((hasDerivAt_id t).sub_const 1).pow 2).const_mul (9 / 2 : ℝ)).add_const (2 * z)).add
    ((((((hasDerivAt_id t).neg.sub_const (2 * z)).add h3).sub (h5.const_mul (3 * z))).sub
      (h7.const_mul (10 * z ^ 2))).const_mul a) |>.add
        ((h3.add (h5.const_mul (2 * z))).const_mul (a ^ 2 / 2))
  convert h using 1
  · funext x
    dsimp [fiberLowerQ] <;> ring
  · norm_num only at h3 h5 h7
    dsimp [fiberLowerQPrime]
    norm_num <;> ring

theorem fiber_hasDerivAt_lower_QPrime {z a t : ℝ} (ht : 0 < t) :
    HasDerivAt (fiberLowerQPrime z a) (fiberLowerQSecond z a t) t := by
  have h5 := Real.hasDerivAt_rpow_const (x := t) (p := -(5 / 2 : ℝ)) (Or.inl ht.ne')
  have h7 := Real.hasDerivAt_rpow_const (x := t) (p := -(7 / 2 : ℝ)) (Or.inl ht.ne')
  have h9 := Real.hasDerivAt_rpow_const (x := t) (p := -(9 / 2 : ℝ)) (Or.inl ht.ne')
  have h := (((hasDerivAt_id t).sub_const 1).const_mul (9 : ℝ)).add
    (((((hasDerivAt_const t (-1 : ℝ)).sub (h5.const_mul (3 / 2 : ℝ))).add
      (h7.const_mul (15 / 2 * z))).add (h9.const_mul (35 * z ^ 2))).const_mul a) |>.add
        (((h5.const_mul (-3 / 2 : ℝ)).sub (h7.const_mul (5 * z))).const_mul (a ^ 2 / 2))
  convert h using 1
  · funext x
    dsimp [fiberLowerQPrime] <;> ring
  · dsimp [fiberLowerQSecond]
    norm_num <;> ring

theorem fiber_lower_QSecond_formula {z a t : ℝ} (ht : 0 < t) :
    fiberLowerQSecond z a t = 9 + a * t ^ (-(11 / 2 : ℝ)) *
      (15 / 4 * (1 + a / 2) * t ^ 2 + 35 * z / 4 * (a - 3) * t - 315 * z ^ 2 / 2) := by
  have h7 : t ^ (-(7 / 2 : ℝ)) = t ^ (-(11 / 2 : ℝ)) * t ^ 2 := by
    rw [show -(7 / 2 : ℝ) = -(11 / 2 : ℝ) + 2 by norm_num, Real.rpow_add ht, Real.rpow_two]
  have h9 : t ^ (-(9 / 2 : ℝ)) = t ^ (-(11 / 2 : ℝ)) * t := by
    rw [show -(9 / 2 : ℝ) = -(11 / 2 : ℝ) + 1 by norm_num, Real.rpow_add ht, Real.rpow_one]
  unfold fiberLowerQSecond
  rw [h7, h9]
  ring

theorem fiber_lower_Q_curvature {a t : ℝ} (ha : 0 ≤ a) (ht : 3 / 5 ≤ t) :
    (9 : ℝ) ≤ fiberLowerQSecond (1 / 19) a t := by
  have ht0 : 0 < t := by linarith
  have hb : 153 / 1805 ≤ 15 / 4 * t ^ 2 - 105 / 4 * (1 / 19) * t -
      315 * (1 / 19 : ℝ) ^ 2 / 2 := by
    have hp : 0 ≤ (t - 3 / 5) * (15 / 4 * (t + 3 / 5) - 105 / 76) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have hplus : 0 ≤ (15 / 8 * t ^ 2 + 35 / 76 * t) * a := by positivity
  have hbrace : 0 ≤ 15 / 4 * (1 + a / 2) * t ^ 2 +
      35 * (1 / 19 : ℝ) / 4 * (a - 3) * t - 315 * (1 / 19 : ℝ) ^ 2 / 2 := by
    nlinarith
  rw [fiber_lower_QSecond_formula ht0]
  have hp := mul_nonneg (mul_nonneg ha (Real.rpow_nonneg ht0.le (-(11 / 2 : ℝ)))) hbrace
  linarith

theorem fiber_lower_Q_reciprocal_concavity {z a t : ℝ}
    (hz0 : 0 ≤ z) (hzh : z ≤ 1 / 19) (ha : 0 ≤ a) (ht : 0 < t) :
    (1 - 19 * z) * fiberLowerQ 0 a t + 19 * z * fiberLowerQ (1 / 19) a t ≤
      fiberLowerQ z a t := by
  have hp : 0 ≤ 10 * a * z * (1 / 19 - z) * t ^ (-(7 / 2 : ℝ)) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha) hz0)
      (by linarith)) (Real.rpow_nonneg ht.le _)
  unfold fiberLowerQ
  nlinarith

end Erdos993Lean.Analytic.V213
