module

public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.Tactic

/-!
# Version 2.2 of the manuscript: exact consecutive Robbins remainder estimates

Source: the Robbins argument used in note Lemma 3.7.
Consumer: the Robbins factorial bounds used in the central binomial mass bound.
This is scalar analytic work on the retained natural factorial index. It does
not construct or reconstruct a forest, selection, ownership, or process record.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real

/-- The positive series parameter for the difference at factorial index `n`. -/
noncomputable def robbinsStepX (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) + 1)

/-- The exact consecutive logarithmic Stirling difference. -/
noncomputable def robbinsLogStep (n : ℕ) : ℝ :=
  Real.log (Stirling.stirlingSeq n) - Real.log (Stirling.stirlingSeq (n + 1))

theorem robbinsStepX_pos (n : ℕ) : 0 < robbinsStepX n := by
  unfold robbinsStepX
  positivity

theorem robbinsStepX_lt_one {n : ℕ} (hn : 1 ≤ n) : robbinsStepX n < 1 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold robbinsStepX
  apply (div_lt_one (by positivity : (0 : ℝ) < 2 * (n : ℝ) + 1)).2
  linarith

theorem robbinsStepX_sq_lt_one {n : ℕ} (hn : 1 ≤ n) : robbinsStepX n ^ 2 < 1 :=
  pow_lt_one₀ (robbinsStepX_pos n).le (robbinsStepX_lt_one hn) (by decide)

/-- The first positive series term strictly exceeds the lower correction
difference; the exact numerator slack is `24*n - 23`. -/
theorem robbins_lower_correction_lt_first_term {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ) + 1) - 1 / (12 * (n : ℝ) + 13) <
      robbinsStepX n ^ 2 / 3 := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have ha : (0 : ℝ) < 12 * (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < 12 * (n : ℝ) + 13 := by positivity
  have hleft :
      1 / (12 * (n : ℝ) + 1) - 1 / (12 * (n : ℝ) + 13) =
        12 / ((12 * (n : ℝ) + 1) * (12 * (n : ℝ) + 13)) := by
    field_simp [ha.ne', hb.ne']
    ring
  have hright : robbinsStepX n ^ 2 / 3 = 1 / (3 * (2 * (n : ℝ) + 1) ^ 2) := by
    unfold robbinsStepX
    field_simp [hd.ne']
  rw [hleft, hright]
  apply (div_lt_div_iff₀ (mul_pos ha hb) (by positivity)).2
  nlinarith

/-- The geometric majorant has exactly the upper correction difference. -/
theorem robbins_geometric_eq_upper_correction {n : ℕ} (hn : 1 ≤ n) :
    robbinsStepX n ^ 2 / (3 * (1 - robbinsStepX n ^ 2)) =
      1 / (12 * (n : ℝ)) - 1 / (12 * ((n : ℝ) + 1)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  have hq : 1 - robbinsStepX n ^ 2 ≠ 0 := ne_of_gt (by
    linarith [robbinsStepX_sq_lt_one hn])
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hden : (2 * (n : ℝ) + 1) ^ 2 - 1 ≠ 0 := ne_of_gt (by
    nlinarith [sq_nonneg (n : ℝ)])
  unfold robbinsStepX at *
  field_simp [hd, hq, hden, hn0, hn1]
  ring_nf

/-- Mathlib's exact series, reindexed to every positive factorial index. -/
theorem robbins_log_step_hasSum {n : ℕ} (hn : 1 ≤ n) :
    HasSum (fun k : ℕ =>
      (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        (robbinsStepX n ^ 2) ^ (k + 1)) (robbinsLogStep n) := by
  cases n with
  | zero => omega
  | succ n =>
    simpa [robbinsLogStep, robbinsStepX, Nat.succ_eq_add_one, Nat.add_assoc] using
      Stirling.log_stirlingSeq_diff_hasSum n

/-- The exact series contains its first nonnegative term. -/
theorem robbins_first_term_le_log_step {n : ℕ} (hn : 1 ≤ n) :
    robbinsStepX n ^ 2 / 3 ≤ robbinsLogStep n := by
  have h := le_hasSum (robbins_log_step_hasSum hn) 0 (fun k _ => by positivity)
  norm_num at h
  linarith

/-- Every exact-series coefficient is at most `1/3`. -/
theorem robbins_series_coefficient_le (k : ℕ) :
    (1 : ℝ) / (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [Nat.cast_add, Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 3)).2
  linarith

/-- The exact series is strictly below its geometric majorant. Strictness
comes from the second positive term, whose coefficient is `1/5`. -/
theorem robbins_log_step_lt_geometric {n : ℕ} (hn : 1 ≤ n) :
    robbinsLogStep n < robbinsStepX n ^ 2 / (3 * (1 - robbinsStepX n ^ 2)) := by
  have hx : 0 < robbinsStepX n := robbinsStepX_pos n
  have hx2 : robbinsStepX n ^ 2 < 1 := robbinsStepX_sq_lt_one hn
  have hgeo0 : HasSum (fun k : ℕ => (robbinsStepX n ^ 2) ^ (k + 1))
      (robbinsStepX n ^ 2 / (1 - robbinsStepX n ^ 2)) := by
    have h := (hasSum_geometric_of_lt_one (sq_nonneg (robbinsStepX n)) hx2).mul_left
      (robbinsStepX n ^ 2)
    simpa only [← pow_succ', div_eq_mul_inv] using h
  have hgeo : HasSum (fun k : ℕ => (1 / 3 : ℝ) * (robbinsStepX n ^ 2) ^ (k + 1))
      (robbinsStepX n ^ 2 / (3 * (1 - robbinsStepX n ^ 2))) := by
    convert hgeo0.mul_left (1 / 3 : ℝ) using 1
    have hq : 1 - robbinsStepX n ^ 2 ≠ 0 := ne_of_gt (sub_pos.mpr hx2)
    field_simp [hq]
  refine hasSum_lt (fun k => ?_) (i := 1) ?_ (robbins_log_step_hasSum hn) hgeo
  · exact mul_le_mul_of_nonneg_right (robbins_series_coefficient_le k) (by positivity)
  · norm_num
    exact mul_lt_mul_of_pos_right (by norm_num : (1 / 5 : ℝ) < 1 / 3) (by positivity)

/-- The two exact strict consecutive inequalities required by Robbins. -/
theorem robbins_log_step_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ) + 1) - 1 / (12 * (n : ℝ) + 13) < robbinsLogStep n ∧
      robbinsLogStep n < 1 / (12 * (n : ℝ)) - 1 / (12 * ((n : ℝ) + 1)) := by
  constructor
  · exact (robbins_lower_correction_lt_first_term hn).trans_le
      (robbins_first_term_le_log_step hn)
  · rw [← robbins_geometric_eq_upper_correction hn]
    exact robbins_log_step_lt_geometric hn

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.robbinsStepX
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsStepX
#check Erdos993Lean.Analytic.V22.Analysis.robbinsLogStep
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsLogStep
#check Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_pos
#check Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_lt_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_lt_one
#check Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_sq_lt_one
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsStepX_sq_lt_one
#check Erdos993Lean.Analytic.V22.Analysis.robbins_lower_correction_lt_first_term
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_lower_correction_lt_first_term
#check Erdos993Lean.Analytic.V22.Analysis.robbins_geometric_eq_upper_correction
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_geometric_eq_upper_correction
#check Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_hasSum
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_hasSum
#check Erdos993Lean.Analytic.V22.Analysis.robbins_first_term_le_log_step
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_first_term_le_log_step
#check Erdos993Lean.Analytic.V22.Analysis.robbins_series_coefficient_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_series_coefficient_le
#check Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_lt_geometric
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_lt_geometric
#check Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_log_step_bounds
