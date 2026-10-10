module

public import Erdos993Lean.Analytic.V213.FiberLowerCoefficientCheck
public import Erdos993Lean.Analytic.V213.FiberLowerDiscriminant
public import Erdos993Lean.Analytic.V213.FiberLowerZeroMean

/-!
Accepted F02 to the actual Eq83 quadratic: canonical coefficient formulas,
point/derivative binding, all a in[0,1] estimates and the positive discriminant.
No bound is a replacement premise. All six reviewed leaves are consumed only
through their typed printed identities and the Int/Nat checked formula shapes.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_lower_coefficient_relation_real (id : FiberLowerCoefficientIdentity) :
    match id with
    | .a0 | .a1 | .a2 => 0 < lowMeanFractionReal (fiberLowerCoefficientById id).difference
    | .v0 => lowMeanFractionReal (fiberLowerCoefficientById id).difference = 0
    | .v1 => 0 ≤ lowMeanFractionReal (fiberLowerCoefficientById id).difference ∧
        lowMeanFractionReal (fiberLowerCoefficientById id).difference ≤ (3 / 10000 : ℝ)
    | .v2 => -(3 / 10000 : ℝ) ≤ lowMeanFractionReal (fiberLowerCoefficientById id).difference ∧
        lowMeanFractionReal (fiberLowerCoefficientById id).difference ≤ 0 := by
  have h := of_decide_eq_true (fiber_lower_named_coefficient_checked id)
  have hd := h.2.2.1
  have hr := h.2.2.2.2.2.2.2.2.2
  have hz : lowMeanFractionValid (0, 1) := by unfold lowMeanFractionValid; decide +kernel
  have hp : lowMeanFractionValid (3, 10000) := by unfold lowMeanFractionValid; decide +kernel
  have hn : lowMeanFractionValid (-3, 10000) := by unfold lowMeanFractionValid; decide +kernel
  cases id with
  | a0 =>
    have hlt := of_decide_eq_true hr
    simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
      (lowMean_fraction_lt_iff hz hd).mp hlt
  | a1 =>
    have hlt := of_decide_eq_true hr
    simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
      (lowMean_fraction_lt_iff hz hd).mp hlt
  | a2 =>
    have hlt := of_decide_eq_true hr
    simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
      (lowMean_fraction_lt_iff hz hd).mp hlt
  | v0 =>
    have he := of_decide_eq_true hr
    simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
      (lowMean_fraction_eq_iff hd hz).mp he
  | v1 =>
    have he := of_decide_eq_true hr
    constructor
    · simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
        (lowMean_fraction_le_iff hz hd).mp he.1
    · simpa only [lowMeanFractionReal, Int.cast_ofNat, Nat.cast_ofNat] using
        (lowMean_fraction_le_iff hd hp).mp he.2
  | v2 =>
    have he := of_decide_eq_true hr
    constructor
    · simpa only [lowMeanFractionReal, Int.cast_neg, Int.cast_ofNat, Nat.cast_ofNat, neg_div] using
        (lowMean_fraction_le_iff hn hd).mp he.1
    · simpa only [lowMeanFractionReal, Int.cast_zero, Nat.cast_one, zero_div] using
        (lowMean_fraction_le_iff hd hz).mp he.2

theorem fiber_lower_Q_point (a : ℝ) :
    fiberLowerQ (1 / 19) a ((11 / 10 : ℝ) ^ 2) =
      lowMeanFractionReal (fiberLowerCoefficientById .a0).actual +
        lowMeanFractionReal (fiberLowerCoefficientById .a1).actual * a +
        lowMeanFractionReal (fiberLowerCoefficientById .a2).actual * a ^ 2 := by
  rw [fiber_lower_Q_root (by norm_num : (0 : ℝ) < (11 / 10 : ℝ) ^ 2),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11 / 10),
    fiber_lower_coefficient_canonical_sound .a0, fiber_lower_coefficient_canonical_sound .a1,
    fiber_lower_coefficient_canonical_sound .a2]
  norm_num [fiberLowerCoefficientCanonical, lowMeanFractionReal, lowMeanFractionAdd,
    lowMeanFractionMul, lowMeanFractionPow]
  ring

theorem fiber_lower_QPrime_point (a : ℝ) :
    fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2) =
      lowMeanFractionReal (fiberLowerCoefficientById .v0).actual +
        lowMeanFractionReal (fiberLowerCoefficientById .v1).actual * a +
        lowMeanFractionReal (fiberLowerCoefficientById .v2).actual * a ^ 2 := by
  rw [fiber_lower_QPrime_root (by norm_num : (0 : ℝ) < (11 / 10 : ℝ) ^ 2),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 11 / 10),
    fiber_lower_coefficient_canonical_sound .v0, fiber_lower_coefficient_canonical_sound .v1,
    fiber_lower_coefficient_canonical_sound .v2]
  norm_num [fiberLowerCoefficientCanonical, lowMeanFractionReal, lowMeanFractionAdd,
    lowMeanFractionMul, lowMeanFractionPow]
  ring

theorem fiber_lower_Q_point_bound {a : ℝ} (ha : 0 ≤ a) :
    fiberLowerAb a ≤ fiberLowerQ (1 / 19) a ((11 / 10 : ℝ) ^ 2) := by
  have h0 := fiber_lower_coefficient_relation_real .a0
  have h1 := fiber_lower_coefficient_relation_real .a1
  have h2 := fiber_lower_coefficient_relation_real .a2
  dsimp only at h0 h1 h2
  rw [fiber_lower_coefficient_difference_sound .a0] at h0
  rw [fiber_lower_coefficient_difference_sound .a1] at h1
  rw [fiber_lower_coefficient_difference_sound .a2] at h2
  have hp1 := mul_nonneg h1.le ha
  have hp2 := mul_nonneg h2.le (sq_nonneg a)
  rw [fiber_lower_Q_point]
  unfold fiberLowerAb
  norm_num only [fiberLowerCoefficientById, lowMeanFractionReal, Int.cast_ofNat,
    Int.cast_neg, Nat.cast_ofNat] at h0 hp1 hp2 ⊢
  nlinarith

theorem fiber_lower_QPrime_point_error {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2) - fiberLowerVb a| ≤
      (3 / 10000 : ℝ) * (a + a ^ 2) ∧
        (3 / 10000 : ℝ) * (a + a ^ 2) < (1 / 1000 : ℝ) := by
  have h0 := fiber_lower_coefficient_relation_real .v0
  have h1 := fiber_lower_coefficient_relation_real .v1
  have h2 := fiber_lower_coefficient_relation_real .v2
  dsimp only at h0 h1 h2
  rw [fiber_lower_coefficient_difference_sound .v0] at h0
  rw [fiber_lower_coefficient_difference_sound .v1] at h1
  rw [fiber_lower_coefficient_difference_sound .v2] at h2
  have hp1lo := mul_nonneg h1.1 ha0
  have hp1hi := mul_le_mul_of_nonneg_right h1.2 ha0
  have hp2lo := mul_le_mul_of_nonneg_right h2.1 (sq_nonneg a)
  have hp2hi := mul_nonpos_of_nonpos_of_nonneg h2.2 (sq_nonneg a)
  have ha2 : a ^ 2 ≤ (1 : ℝ) := by nlinarith
  constructor
  · rw [fiber_lower_QPrime_point, abs_le]
    unfold fiberLowerVb
    norm_num only [fiberLowerCoefficientById, lowMeanFractionReal, Int.cast_ofNat,
      Int.cast_neg, Nat.cast_ofNat] at h0 hp1lo hp1hi hp2lo hp2hi ⊢
    constructor <;> nlinarith
  · nlinarith


theorem fiber_lower_QPrime_point_bound {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |fiberLowerQPrime (1 / 19) a ((11 / 10 : ℝ) ^ 2) - fiberLowerVb a| ≤ (1 / 1000 : ℝ) :=
  (fiber_lower_QPrime_point_error ha0 ha1).1.trans (fiber_lower_QPrime_point_error ha0 ha1).2.le

theorem fiber_lower_Q_one_nineteenth {a t : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (ht : 3 / 5 ≤ t) : (1 / 72 : ℝ) < fiberLowerQ (1 / 19) a t :=
  fiber_lower_Q_positive_of_point ha0 ha1 (fiber_lower_Q_point_bound ha0)
    (fiber_lower_QPrime_point_bound ha0 ha1) ht

theorem fiber_lower_Q_margin {z a t : ℝ} (hz0 : 0 < z) (hzh : z ≤ 1 / 19)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (ht : 3 / 5 ≤ t) : z / 4 < fiberLowerQ z a t := by
  have ht0 : 0 < t := by linarith
  have h0 := fiber_lower_Q_zero_nonneg ht ha0 ha1
  have h1 := fiber_lower_Q_one_nineteenth ha0 ha1 ht
  have hc := fiber_lower_Q_reciprocal_concavity hz0.le hzh ha0 ht0
  have hbase := mul_nonneg (by linarith : 0 ≤ 1 - 19 * z) h0
  have hstrict := mul_lt_mul_of_pos_left h1 (by positivity : 0 < 19 * z)
  linarith

end Erdos993Lean.Analytic.V213
