module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

theorem quadratic_complete (a b c y : ℝ) (ha : a ≠ 0) :
    a * y ^ 2 + b * y + c =
      a * (y + b / (2 * a)) ^ 2 + (4 * a * c - b ^ 2) / (4 * a) := by
  field_simp
  <;> ring

theorem quadratic_lower_bound (a b c y : ℝ) (ha : 0 < a) :
    (4 * a * c - b ^ 2) / (4 * a) ≤ a * y ^ 2 + b * y + c := by
  rw [quadratic_complete a b c y (ne_of_gt ha)]
  exact le_add_of_nonneg_left (mul_nonneg ha.le (sq_nonneg _))

theorem quadratic_attains (a b c : ℝ) (ha : a ≠ 0) :
    a * (-b / (2 * a)) ^ 2 + b * (-b / (2 * a)) + c =
      (4 * a * c - b ^ 2) / (4 * a) := by
  rw [quadratic_complete a b c _ ha]
  simp [neg_div]

theorem quadratic_positive (a b c y : ℝ) (ha : 0 < a)
    (hdisc : 0 < 4 * a * c - b ^ 2) :
    0 < a * y ^ 2 + b * y + c := by
  exact lt_of_lt_of_le (div_pos hdisc (mul_pos (by norm_num) ha))
    (quadratic_lower_bound a b c y ha)

theorem quadratic_has_minimum (a b c : ℝ) (ha : 0 < a) :
    (∀ y : ℝ, (4 * a * c - b ^ 2) / (4 * a) ≤ a * y ^ 2 + b * y + c) ∧
    (∃ y : ℝ, a * y ^ 2 + b * y + c = (4 * a * c - b ^ 2) / (4 * a)) := by
  exact ⟨fun y => quadratic_lower_bound a b c y ha,
    ⟨-b / (2 * a), quadratic_attains a b c (ne_of_gt ha)⟩⟩

-- This is the response polynomial used by the support-envelope argument.
noncomputable def responsePolynomial (a b c d delta L h y : ℝ) : ℝ :=
  a + b * h + c * y + d * y ^ 2 + delta / L * (h - y) ^ 2

def responseNumerator (a b c d delta L h : ℝ) : ℝ :=
  4 * (delta + d * L) * (a + b * h) +
    4 * delta * (c * h + d * h ^ 2) - L * c ^ 2

theorem response_complete (a b c d delta L h y : ℝ) (hL : L ≠ 0)
    (hG : delta + d * L ≠ 0) :
    responsePolynomial a b c d delta L h y =
      responseNumerator a b c d delta L h / (4 * (delta + d * L)) +
      (delta + d * L) / L *
        (y - (delta * h - L * c / 2) / (delta + d * L)) ^ 2 := by
  unfold responsePolynomial responseNumerator
  field_simp
  <;> ring

theorem response_positive (a b c d delta L h y : ℝ) (hL : 0 < L)
    (hG : 0 < delta + d * L)
    (hW : 0 < responseNumerator a b c d delta L h) :
    0 < responsePolynomial a b c d delta L h y := by
  rw [response_complete a b c d delta L h y (ne_of_gt hL) (ne_of_gt hG)]
  exact add_pos_of_pos_of_nonneg (div_pos hW (mul_pos (by norm_num) hG))
    (mul_nonneg (div_pos hG hL).le (sq_nonneg _))

theorem response_zero_envelope (a b c d delta h : ℝ) :
    responsePolynomial a b c d delta 0 h h = a + (b + c) * h + d * h ^ 2 := by
  unfold responsePolynomial
  simp
  <;> ring

theorem response_obstruction (a b c d delta L h : ℝ) :
    responseNumerator a b c d delta L h =
      4 * (delta + d * L) * (a + (b + c) * h + d * h ^ 2) -
        L * (c + 2 * d * h) ^ 2 := by
  unfold responseNumerator
  ring

theorem response_denominator_ne_zero (a b c d delta L h : ℝ) (hL : 0 ≤ L)
    (hW : 0 < responseNumerator a b c d delta L h) :
    delta + d * L ≠ 0 := by
  intro hzero
  rw [response_obstruction, hzero] at hW
  have hs := mul_nonneg hL (sq_nonneg (c + 2 * d * h))
  nlinarith

end F4Heavy.Analysis
