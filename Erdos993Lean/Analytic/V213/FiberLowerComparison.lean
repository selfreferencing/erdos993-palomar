module

public import Erdos993Lean.Analytic.V213.FiberLowerBranches
public import Erdos993Lean.Analytic.V213.FiberLowerBudget
public import Erdos993Lean.Analytic.V213.FiberLowerCoefficientConsequences
public import Erdos993Lean.Analytic.V213.FiberMassLinearization

/-!
Full Theorem 6.13 on every natural width and integer rank.
The actual Eq75 mass gain, strict Eq74 error, Eq81/82 budget and accepted
F02 coefficient checks are composed into the literal Eq83 quadratic.
The small-ratio branch includes M=0. No paper theorem or numeric bound
is retained as an unproved premise in the final comparison.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Real

theorem fiber_bonus_at_least_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (M : ℕ) :
    1 ≤ fiberBonus q M := by
  rw [fiber_bonus_current_formula hq0 hq1 M]
  have hi : 0 ≤ (1 : ℝ) / ((M : ℝ) + 2) := by positivity
  have hh : 0 ≤ ((M : ℝ) + 2) - 1 + 1 / ((M : ℝ) + 2) := by
    linarith [Nat.cast_nonneg (α := ℝ) M]
  nlinarith [mul_nonneg hh (sq_nonneg (fiberSkew q / Real.sqrt (1 - fiberSkew q ^ 2)))]

theorem fiber_lower_xi_bounds {r : ℝ} (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) :
    0 ≤ r / Real.sqrt (1 - r ^ 2) ∧
      (r / Real.sqrt (1 - r ^ 2)) ^ 2 ≤ 1 / 3 := by
  have ha : 0 < 1 - r ^ 2 := by nlinarith
  constructor
  · exact div_nonneg hr0 (Real.sqrt_nonneg _)
  · rw [div_pow, Real.sq_sqrt ha.le]
    apply (div_le_iff₀ ha).2
    nlinarith

theorem fiber_lower_simple_mass_gain {M : ℕ} (hM : 12 ≤ M) {q mu : ℝ}
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (hmu : 0 < mu) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ 1) :
    fiberSquareOffset q M j + (1 - fiberSquareOffset q M j) *
      ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
        (1 + (1 - fiberSquareOffset q M j) / 2 - 5 / (M : ℝ)) ≤
      fiberF q mu M j / (((M : ℝ) + 2) / mu) := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hr0 : 0 ≤ fiberSkew q := by unfold fiberSkew; linarith
  have hrh : fiberSkew q ≤ 1 / 2 := by unfold fiberSkew; linarith
  have hN : (14 : ℝ) ≤ (M : ℝ) + 2 := by exact_mod_cast (by omega : 14 ≤ M + 2)
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ht : 0 < (M : ℝ) / mu := div_pos hM0 hmu
  have hxi := fiber_lower_xi_bounds hr0 hrh
  have he := (fiber_mass_error_w1_n14 hN hr0 hrh).2
  have hs := fiber_lower_scalar_gain hN (fiber_square_offset_nonneg hq0' hq1 M j)
    hw hxi.1 hxi.2 ht he
  have hm := fiber_lower_mass_gain_used_windows hM hq0 hqh hmu
    (by norm_num : (1 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 3 / 2) j hw
    (fiber_bonus_at_least_one hq0' hq1 M)
  have hs' : fiberSquareOffset q M j + (1 - fiberSquareOffset q M j) *
      ((M : ℝ) / mu) ^ (-(5 / 2 : ℝ)) *
        (1 + (1 - fiberSquareOffset q M j) / 2 - 5 / (M : ℝ)) ≤
      fiberLowerMassGain q mu M j 1 := by
    simp only [fiberLowerH, fiberLowerShiftBound,
      show (M : ℝ) + 2 - 2 = (M : ℝ) by ring,
      show (M : ℝ) + 2 + 1 = (M : ℝ) + 3 by ring] at hs
    unfold fiberLowerMassGain fiberLowerMassWeight
    convert hs using 1 <;> congr 1 <;> ring
  exact hs'.trans hm

theorem fiber_lower_Q_gain_identity {z a t : ℝ} (ht : 0 < t) :
    (t + 2 * z) * (1 - a + a * t ^ (-(5 / 2 : ℝ)) * (1 + a / 2 - 5 * z / t)) -
      fiberPsi t = fiberLowerQ z a t := by
  have h3 : t ^ (-(3 / 2 : ℝ)) = t * t ^ (-(5 / 2 : ℝ)) := by
    calc
      _ = t ^ ((1 : ℝ) + -(5 / 2 : ℝ)) := by congr 1; norm_num
      _ = t ^ (1 : ℝ) * t ^ (-(5 / 2 : ℝ)) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  have h5 : t ^ (-(5 / 2 : ℝ)) = t * t ^ (-(7 / 2 : ℝ)) := by
    calc
      _ = t ^ ((1 : ℝ) + -(7 / 2 : ℝ)) := by congr 1; norm_num
      _ = t ^ (1 : ℝ) * t ^ (-(7 / 2 : ℝ)) := Real.rpow_add ht _ _
      _ = _ := by rw [Real.rpow_one]
  unfold fiberPsi fiberLowerQ
  rw [h3, h5]
  field_simp [ht.ne']
  ring

theorem fiber_lower_offset_comparison {q mu : ℝ} (hmu : 19 ≤ mu)
    (hq0 : 1 / 2 ≤ q) (hqh : q ≤ 3 / 4) (M : ℕ) (j : ℤ)
    (hw : fiberSquareOffset q M j ≤ fiberBonus q M) :
    fiberPsi ((M : ℝ) / mu) + 1 / (4 * mu) ≤ fiberF q mu M j := by
  have hq0' : 0 < q := by linarith
  have hq1 : q < 1 := by linarith
  have hmu0 : 0 < mu := by linarith
  by_cases ht : (M : ℝ) / mu ≤ 3 / 5
  · exact fiber_lower_small_ratio hq0' hq1 hmu M j hw ht
  have ht' : 3 / 5 ≤ (M : ℝ) / mu := le_of_lt (lt_of_not_ge ht)
  have hM := fiber_lower_integer_width hmu ht'
  by_cases hw1 : 1 ≤ fiberSquareOffset q M j
  · exact fiber_lower_at_least_one hq0' hq1 hmu0 M j hw hw1
  have hw' : fiberSquareOffset q M j ≤ 1 := le_of_lt (lt_of_not_ge hw1)
  have hw0 := fiber_square_offset_nonneg hq0' hq1 M j
  have hM0 : 0 < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have ht0 : 0 < (M : ℝ) / mu := div_pos hM0 hmu0
  have hz0 : 0 < (1 : ℝ) / mu := one_div_pos.mpr hmu0
  have hzh : (1 : ℝ) / mu ≤ 1 / 19 :=
    one_div_le_one_div_of_le (by norm_num) hmu
  have hQ := fiber_lower_Q_margin hz0 hzh (by linarith : 0 ≤ 1 - fiberSquareOffset q M j)
    (by linarith : 1 - fiberSquareOffset q M j ≤ 1) ht'
  have hg := fiber_lower_simple_mass_gain hM hq0 hqh hmu0 j hw'
  have hB : 0 < ((M : ℝ) + 2) / mu := by positivity
  have hgain := (le_div_iff₀ hB).mp hg
  have hB_eq : ((M : ℝ) + 2) / mu = (M : ℝ) / mu + 2 * (1 / mu) := by ring
  have hfrac : 5 / (M : ℝ) = 5 * (1 / mu) / ((M : ℝ) / mu) := by
    field_simp [hM0.ne', hmu0.ne']
  have hi := fiber_lower_Q_gain_identity (z := 1 / mu)
    (a := 1 - fiberSquareOffset q M j) ht0
  rw [hB_eq, hfrac] at hgain
  have he : (1 / mu) / 4 = (1 : ℝ) / (4 * mu) := by ring
  rw [he] at hQ
  nlinarith [hi]

/-- Literal Theorem 6.13 with the paper's skew parameter and global width/rank domains. -/
theorem fiber_lower_offset_comparison_skew {r mu : ℝ} (hmu : 19 ≤ mu)
    (hr0 : 0 ≤ r) (hrh : r ≤ 1 / 2) (M : ℕ) (j : ℤ)
    (hw : fiberSquareOffset ((1 + r) / 2) M j ≤ fiberBonus ((1 + r) / 2) M) :
    fiberF ((1 + r) / 2) mu M j ≥ fiberPsi ((M : ℝ) / mu) + 1 / (4 * mu) :=
  fiber_lower_offset_comparison hmu (by linarith) (by linarith) M j hw

end Erdos993Lean.Analytic.V213
