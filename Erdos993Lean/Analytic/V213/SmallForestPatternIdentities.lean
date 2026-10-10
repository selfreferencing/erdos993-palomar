module

public import Erdos993Lean.Analytic.V213.SmallForestPatternQuotients

/-!
Nine universal printed symbolic patterns.
The parameter n is arbitrary and j=n+j0, so no finite-index testing is used.
The offsets below are exactly t=2j+u and M=2j+nu. The reviewed Rat
operands are connected to these Real extensions by quotientN_cast.

-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.SmallForestPatterns

open Erdos993Lean.Analytic.V213.SmallForest

/-- Printed row 1, exact residual identity for every j=n+7. -/
theorem pattern1_residual (n : ℕ) :
    G (1/2) ((n+7 : ℕ) : ℤ) (2*n+15) - G (1/2) ((n+7 : ℕ) : ℤ) (2*n+10) - 5*(G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9)) =
      ratio1 ((n : ℝ)+7) * (G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+7+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+7+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+7+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+7+4 ≠ 0 := by positivity
  have hd0 : (n : ℝ)+7-6 ≠ 0 := by linarith
  have h := pattern_residual_of_identity (1/2) (ratio1 ((n : ℝ)+7))
    (n+7) (2*n+10) 5 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio1, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4, hd0]
      <;> ring)
  simpa only [show 2*n+10+5=2*n+15 by omega,
    show 2*n+10-1=2*n+9 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 1. -/
theorem pattern1_signs (n : ℕ) :
    0 < G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9) ∧ 0 < G (1/2) (((n+7 : ℕ) : ℤ)-2) (2*n+8) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+6) (2*n+9)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+6 : ℕ) : ℤ) = ((n+7 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+5) (2*n+8)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+5 : ℕ) : ℤ) = ((n+7 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 1. -/
theorem pattern1_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+7 : ℕ) : ℤ) (2*n+15) - G (1/2) ((n+7 : ℕ) : ℤ) (2*n+10) - 5*(G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9))) / (G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9)) = ratio1 ((n : ℝ)+7) ∧
      0 ≤ G (1/2) ((n+7 : ℕ) : ℤ) (2*n+15) - G (1/2) ((n+7 : ℕ) : ℤ) (2*n+10) - 5*(G (1/2) (((n+7 : ℕ) : ℤ)-1) (2*n+9)) := by
  have hq := (pattern1_signs n).1
  have hR := pattern1_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio1_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 2, exact residual identity for every j=n+4. -/
theorem pattern2_residual (n : ℕ) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+5) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4)) =
      ratio2 ((n : ℝ)+4) * (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+4+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+4+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+4+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+4+4 ≠ 0 := by positivity
  have hd0 : (n : ℝ)+4-3 ≠ 0 := by linarith
  have h := pattern_residual_of_identity (1/2) (ratio2 ((n : ℝ)+4))
    (n+4) (2*n+5) 5 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio2, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4, hd0]
      <;> ring)
  simpa only [show 2*n+5+5=2*n+10 by omega,
    show 2*n+5-1=2*n+4 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 2. -/
theorem pattern2_signs (n : ℕ) :
    0 < G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4) ∧ 0 < G (1/2) (((n+4 : ℕ) : ℤ)-2) (2*n+3) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+3) (2*n+4)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+3 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+2) (2*n+3)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 2. -/
theorem pattern2_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+5) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4))) / (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4)) = ratio2 ((n : ℝ)+4) ∧
      0 ≤ G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+5) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+4)) := by
  have hq := (pattern2_signs n).1
  have hR := pattern2_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio2_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 3, exact residual identity for every j=n+2. -/
theorem pattern3_residual (n : ℕ) :
    G (1/2) ((n+2 : ℕ) : ℤ) (2*n+6) - G (1/2) ((n+2 : ℕ) : ℤ) (2*n+2) - 4*(G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1)) =
      ratio3 ((n : ℝ)+2) * (G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+2+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+2+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+2+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+2+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (1/2) (ratio3 ((n : ℝ)+2))
    (n+2) (2*n+2) 4 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio3, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+2+4=2*n+6 by omega,
    show 2*n+2-1=2*n+1 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 3. -/
theorem pattern3_signs (n : ℕ) :
    0 < G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1) ∧ 0 < G (1/2) (((n+2 : ℕ) : ℤ)-2) (2*n+0) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+1) (2*n+1)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+1 : ℕ) : ℤ) = ((n+2 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have he : (n : ℤ) = ((n+2 : ℕ) : ℤ)-2 := by omega
    rw [← he]
    by_cases hn0 : n=0
    · subst n
      norm_num [G_zero_index]
    · apply G_pos_of_quad_pos (1/2) n (2*n+0) (by omega) (by omega)
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      norm_num [GQuad] <;> nlinarith

/-- Literal quotient equality and nonnegative endpoint residual, row 3. -/
theorem pattern3_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+2 : ℕ) : ℤ) (2*n+6) - G (1/2) ((n+2 : ℕ) : ℤ) (2*n+2) - 4*(G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1))) / (G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1)) = ratio3 ((n : ℝ)+2) ∧
      0 ≤ G (1/2) ((n+2 : ℕ) : ℤ) (2*n+6) - G (1/2) ((n+2 : ℕ) : ℤ) (2*n+2) - 4*(G (1/2) (((n+2 : ℕ) : ℤ)-1) (2*n+1)) := by
  have hq := (pattern3_signs n).1
  have hR := pattern3_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio3_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 4, exact residual identity for every j=n+4. -/
theorem pattern4_residual (n : ℕ) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+11) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+6) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5)) =
      ratio4 ((n : ℝ)+4) * (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+4+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+4+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+4+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+4+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (1/2) (ratio4 ((n : ℝ)+4))
    (n+4) (2*n+6) 5 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio4, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+6+5=2*n+11 by omega,
    show 2*n+6-1=2*n+5 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 4. -/
theorem pattern4_signs (n : ℕ) :
    0 < G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5) ∧ 0 < G (1/2) (((n+4 : ℕ) : ℤ)-2) (2*n+4) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+3) (2*n+5)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+3 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+2) (2*n+4)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 4. -/
theorem pattern4_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+4 : ℕ) : ℤ) (2*n+11) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+6) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5))) / (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5)) = ratio4 ((n : ℝ)+4) ∧
      0 ≤ G (1/2) ((n+4 : ℕ) : ℤ) (2*n+11) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+6) - 5*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+5)) := by
  have hq := (pattern4_signs n).1
  have hR := pattern4_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio4_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 5, exact residual identity for every j=n+3. -/
theorem pattern5_residual (n : ℕ) :
    G (1/2) ((n+3 : ℕ) : ℤ) (2*n+7) - G (1/2) ((n+3 : ℕ) : ℤ) (2*n+5) - 2*(G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4)) =
      ratio5 ((n : ℝ)+3) * (G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+3+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+3+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+3+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+3+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (1/2) (ratio5 ((n : ℝ)+3))
    (n+3) (2*n+5) 2 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio5, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+5+2=2*n+7 by omega,
    show 2*n+5-1=2*n+4 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 5. -/
theorem pattern5_signs (n : ℕ) :
    0 < G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4) ∧ 0 < G (1/2) (((n+3 : ℕ) : ℤ)-2) (2*n+3) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+2) (2*n+4)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+3 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+1) (2*n+3)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+1 : ℕ) : ℤ) = ((n+3 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 5. -/
theorem pattern5_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+3 : ℕ) : ℤ) (2*n+7) - G (1/2) ((n+3 : ℕ) : ℤ) (2*n+5) - 2*(G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4))) / (G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4)) = ratio5 ((n : ℝ)+3) ∧
      0 ≤ G (1/2) ((n+3 : ℕ) : ℤ) (2*n+7) - G (1/2) ((n+3 : ℕ) : ℤ) (2*n+5) - 2*(G (1/2) (((n+3 : ℕ) : ℤ)-1) (2*n+4)) := by
  have hq := (pattern5_signs n).1
  have hR := pattern5_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio5_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 6, exact residual identity for every j=n+4. -/
theorem pattern6_residual (n : ℕ) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+7) - 3*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6)) =
      ratio6 ((n : ℝ)+4) * (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+4+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+4+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+4+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+4+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (1/2) (ratio6 ((n : ℝ)+4))
    (n+4) (2*n+7) 3 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio6, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+7+3=2*n+10 by omega,
    show 2*n+7-1=2*n+6 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 6. -/
theorem pattern6_signs (n : ℕ) :
    0 < G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6) ∧ 0 < G (1/2) (((n+4 : ℕ) : ℤ)-2) (2*n+5) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+3) (2*n+6)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+3 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+2) (2*n+5)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 6. -/
theorem pattern6_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+7) - 3*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6))) / (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6)) = ratio6 ((n : ℝ)+4) ∧
      0 ≤ G (1/2) ((n+4 : ℕ) : ℤ) (2*n+10) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+7) - 3*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+6)) := by
  have hq := (pattern6_signs n).1
  have hR := pattern6_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio6_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 7, exact residual identity for every j=n+4. -/
theorem pattern7_residual (n : ℕ) :
    G (1/2) ((n+4 : ℕ) : ℤ) (2*n+9) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+8) - 1*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7)) =
      ratio7 ((n : ℝ)+4) * (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+4+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+4+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+4+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+4+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (1/2) (ratio7 ((n : ℝ)+4))
    (n+4) (2*n+8) 1 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio7, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+8+1=2*n+9 by omega,
    show 2*n+8-1=2*n+7 by omega, Nat.cast_ofNat, Nat.cast_one] using h

/-- Both strict signs required by the supporting-line lemma, row 7. -/
theorem pattern7_signs (n : ℕ) :
    0 < G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7) ∧ 0 < G (1/2) (((n+4 : ℕ) : ℤ)-2) (2*n+6) := by
  constructor
  · have h := G_pos_of_quad_pos (1/2) (n+3) (2*n+7)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+3 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (1/2) (n+2) (2*n+6)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+4 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 7. -/
theorem pattern7_quotient_and_endpoint (n : ℕ) :
    (G (1/2) ((n+4 : ℕ) : ℤ) (2*n+9) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+8) - 1*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7))) / (G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7)) = ratio7 ((n : ℝ)+4) ∧
      0 ≤ G (1/2) ((n+4 : ℕ) : ℤ) (2*n+9) - G (1/2) ((n+4 : ℕ) : ℤ) (2*n+8) - 1*(G (1/2) (((n+4 : ℕ) : ℤ)-1) (2*n+7)) := by
  have hq := (pattern7_signs n).1
  have hR := pattern7_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio7_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 8, exact residual identity for every j=n+2. -/
theorem pattern8_residual (n : ℕ) :
    G (2/3) ((n+2 : ℕ) : ℤ) (2*n+7) - G (2/3) ((n+2 : ℕ) : ℤ) (2*n+3) - 4*(G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2)) =
      ratio8 ((n : ℝ)+2) * (G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+2+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+2+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+2+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+2+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (2/3) (ratio8 ((n : ℝ)+2))
    (n+2) (2*n+3) 4 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio8, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+3+4=2*n+7 by omega,
    show 2*n+3-1=2*n+2 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 8. -/
theorem pattern8_signs (n : ℕ) :
    0 < G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2) ∧ 0 < G (2/3) (((n+2 : ℕ) : ℤ)-2) (2*n+1) := by
  constructor
  · have h := G_pos_of_quad_pos (2/3) (n+1) (2*n+2)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+1 : ℕ) : ℤ) = ((n+2 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have he : (n : ℤ) = ((n+2 : ℕ) : ℤ)-2 := by omega
    rw [← he]
    by_cases hn0 : n=0
    · subst n
      norm_num [G_zero_index]
    · apply G_pos_of_quad_pos (2/3) n (2*n+1) (by omega) (by omega)
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      norm_num [GQuad] <;> nlinarith

/-- Literal quotient equality and nonnegative endpoint residual, row 8. -/
theorem pattern8_quotient_and_endpoint (n : ℕ) :
    (G (2/3) ((n+2 : ℕ) : ℤ) (2*n+7) - G (2/3) ((n+2 : ℕ) : ℤ) (2*n+3) - 4*(G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2))) / (G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2)) = ratio8 ((n : ℝ)+2) ∧
      0 ≤ G (2/3) ((n+2 : ℕ) : ℤ) (2*n+7) - G (2/3) ((n+2 : ℕ) : ℤ) (2*n+3) - 4*(G (2/3) (((n+2 : ℕ) : ℤ)-1) (2*n+2)) := by
  have hq := (pattern8_signs n).1
  have hR := pattern8_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio8_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

/-- Printed row 9, exact residual identity for every j=n+3. -/
theorem pattern9_residual (n : ℕ) :
    G (2/3) ((n+3 : ℕ) : ℤ) (2*n+8) - G (2/3) ((n+3 : ℕ) : ℤ) (2*n+6) - 2*(G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5)) =
      ratio9 ((n : ℝ)+3) * (G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5)) := by
  have hn : (0 : ℝ) ≤ n := by positivity
  have hd1 : (n : ℝ)+3+1 ≠ 0 := by positivity
  have hd2 : (n : ℝ)+3+2 ≠ 0 := by positivity
  have hd3 : (n : ℝ)+3+3 ≠ 0 := by positivity
  have hd4 : (n : ℝ)+3+4 ≠ 0 := by positivity
  have h := pattern_residual_of_identity (2/3) (ratio9 ((n : ℝ)+3))
    (n+3) (2*n+6) 2 (by omega) (by omega) (by
      simp only [risingR, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_zero, Nat.cast_one]
      dsimp only [ratio9, prod2R, prod3R, prod4R, P3R, P4R, GQuad]
      field_simp [hd1, hd2, hd3, hd4]
      <;> ring)
  simpa only [show 2*n+6+2=2*n+8 by omega,
    show 2*n+6-1=2*n+5 by omega, Nat.cast_ofNat] using h

/-- Both strict signs required by the supporting-line lemma, row 9. -/
theorem pattern9_signs (n : ℕ) :
    0 < G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5) ∧ 0 < G (2/3) (((n+3 : ℕ) : ℤ)-2) (2*n+4) := by
  constructor
  · have h := G_pos_of_quad_pos (2/3) (n+2) (2*n+5)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+2 : ℕ) : ℤ) = ((n+3 : ℕ) : ℤ)-1 := by omega
    rw [he] at h
    exact h
  · have h := G_pos_of_quad_pos (2/3) (n+1) (2*n+4)
      (by omega) (by omega) (by
        have hn : (0 : ℝ) ≤ n := by positivity
        norm_num [GQuad] <;> nlinarith)
    have he : ((n+1 : ℕ) : ℤ) = ((n+3 : ℕ) : ℤ)-2 := by omega
    rw [he] at h
    exact h

/-- Literal quotient equality and nonnegative endpoint residual, row 9. -/
theorem pattern9_quotient_and_endpoint (n : ℕ) :
    (G (2/3) ((n+3 : ℕ) : ℤ) (2*n+8) - G (2/3) ((n+3 : ℕ) : ℤ) (2*n+6) - 2*(G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5))) / (G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5)) = ratio9 ((n : ℝ)+3) ∧
      0 ≤ G (2/3) ((n+3 : ℕ) : ℤ) (2*n+8) - G (2/3) ((n+3 : ℕ) : ℤ) (2*n+6) - 2*(G (2/3) (((n+3 : ℕ) : ℤ)-1) (2*n+5)) := by
  have hq := (pattern9_signs n).1
  have hR := pattern9_residual n
  constructor
  · rw [hR]
    exact mul_div_cancel_right₀ _ (ne_of_gt hq)
  · rw [hR]
    exact mul_nonneg (ratio9_nonneg _ (by
      have hn : (0 : ℝ) ≤ n := by positivity
      linarith)) (le_of_lt hq)

end Erdos993Lean.Analytic.V213.SmallForestPatterns

#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern1_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern2_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern3_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern4_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern5_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern6_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern7_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern8_quotient_and_endpoint
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_residual
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_residual
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_signs
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_signs
#check Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_quotient_and_endpoint
#print axioms Erdos993Lean.Analytic.V213.SmallForestPatterns.pattern9_quotient_and_endpoint
