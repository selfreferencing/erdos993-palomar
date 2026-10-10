module

public import Erdos993Lean.Analytic.V22.Analysis.RobbinsStep

/-!
# Version 2.2 of the manuscript, Lemma 3.7: Robbins' factorial remainder

The consecutive estimates are telescoped through Mathlib's proved Stirling
limit. No finite-check hypothesis is used. The natural factorial index survives
verbatim; this analytic lemma creates no forest/process data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Filter
open scoped Topology

/-- The exact logarithmic remainder in Robbins' formula. -/
noncomputable def robbinsRemainder (n : ℕ) : ℝ :=
  log (Stirling.stirlingSeq n) - log (sqrt π)

theorem robbinsRemainder_tendsto_zero :
    Tendsto robbinsRemainder atTop (𝓝 0) := by
  have h := (Stirling.tendsto_stirlingSeq_sqrt_pi.log (by positivity)).sub
    (tendsto_const_nhds (x := log (sqrt π)))
  change Tendsto (fun n : ℕ => log (Stirling.stirlingSeq n) - log (sqrt π)) atTop (𝓝 0)
  simpa only [sub_self] using h

theorem robbins_correction_tendsto_zero (c : ℝ) :
    Tendsto (fun n : ℕ => 1 / (12 * ((n : ℝ) + 1) + c)) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => 12 * ((n : ℝ) + 1) + c) atTop atTop :=
    ((hcast.atTop_add tendsto_const_nhds).const_mul_atTop (by norm_num)).atTop_add
      tendsto_const_nhds
  exact hden.const_div_atTop 1

/-- Robbins' exact strict remainder bounds, as quoted in note Lemma 3.7. -/
theorem robbins_remainder_bounds {n : ℕ} (hn : 1 ≤ n) :
    1 / (12 * (n : ℝ) + 1) < robbinsRemainder n ∧
      robbinsRemainder n < 1 / (12 * (n : ℝ)) := by
  let lower : ℕ → ℝ := fun k =>
    robbinsRemainder (k + 1) - 1 / (12 * ((k : ℝ) + 1) + 1)
  let upper : ℕ → ℝ := fun k =>
    robbinsRemainder (k + 1) - 1 / (12 * ((k : ℝ) + 1))
  have hlstep (k : ℕ) : lower (k + 1) < lower k := by
    have h := (robbins_log_step_bounds (n := k + 1) (by omega)).1
    dsimp [lower, robbinsRemainder]
    simp only [robbinsLogStep, Nat.cast_add, Nat.cast_one] at h
    simp only [Nat.cast_add, Nat.cast_one]
    have hd : 12 * ((k : ℝ) + 1 + 1) + 1 = 12 * ((k : ℝ) + 1) + 13 := by ring
    rw [hd]
    linarith
  have hustep (k : ℕ) : upper k < upper (k + 1) := by
    have h := (robbins_log_step_bounds (n := k + 1) (by omega)).2
    dsimp [upper, robbinsRemainder]
    simp only [robbinsLogStep, Nat.cast_add, Nat.cast_one] at h
    simp only [Nat.cast_add, Nat.cast_one]
    linarith
  have hr := robbinsRemainder_tendsto_zero.comp (tendsto_add_atTop_nat 1)
  have hl : Tendsto lower atTop (𝓝 0) := by
    simpa [lower] using hr.sub (robbins_correction_tendsto_zero 1)
  have hu : Tendsto upper atTop (𝓝 0) := by
    simpa [upper] using hr.sub (robbins_correction_tendsto_zero 0)
  have hl0 (k : ℕ) : 0 ≤ lower k :=
    (antitone_nat_of_succ_le (fun j => (hlstep j).le)).le_of_tendsto hl k
  have hu0 (k : ℕ) : upper k ≤ 0 :=
    (monotone_nat_of_le_succ (fun j => (hustep j).le)).ge_of_tendsto hu k
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  constructor
  · have h := (hl0 (k + 1)).trans_lt (hlstep k)
    dsimp [lower] at h
    simpa [Nat.add_comm, Nat.cast_add, Nat.cast_one] using
      (sub_pos.mp h)
  · have h := (hustep k).trans_le (hu0 (k + 1))
    dsimp [upper] at h
    simpa [Nat.add_comm, Nat.cast_add, Nat.cast_one] using
      (sub_neg.mp h)

/-- The exact factorial representation used by note Lemma 3.7. -/
theorem factorial_eq_robbins {n : ℕ} (hn : 1 ≤ n) :
    (n.factorial : ℝ) = sqrt (2 * π * n) * ((n : ℝ) / exp 1) ^ n *
      exp (robbinsRemainder n) := by
  have hn0 : n ≠ 0 := by omega
  have hp : 0 < Stirling.stirlingSeq n := by
    cases n with
    | zero => contradiction
    | succ k => exact Stirling.stirlingSeq'_pos k
  have hs : 0 < sqrt π := by positivity
  rw [robbinsRemainder, Real.exp_sub, Real.exp_log hp, Real.exp_log hs]
  have hroot : sqrt (2 * π * (n : ℝ)) = sqrt π * sqrt (2 * (n : ℝ)) := by
    rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ π)]
    congr 1
    ring
  rw [hroot, Stirling.stirlingSeq]
  field_simp

/-- Conventional strict Robbins bounds for every positive factorial index;
source: the displayed Robbins formula in note Lemma 3.7. -/
theorem robbins_factorial_bounds {n : ℕ} (hn : 1 ≤ n) :
    sqrt (2 * π * n) * ((n : ℝ) / exp 1) ^ n *
        exp (1 / (12 * (n : ℝ) + 1)) < (n.factorial : ℝ) ∧
      (n.factorial : ℝ) < sqrt (2 * π * n) * ((n : ℝ) / exp 1) ^ n *
        exp (1 / (12 * (n : ℝ))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hp : 0 < sqrt (2 * π * n) * ((n : ℝ) / exp 1) ^ n := by positivity
  rw [factorial_eq_robbins hn]
  exact ⟨mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (robbins_remainder_bounds hn).1) hp,
    mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr (robbins_remainder_bounds hn).2) hp⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.robbinsRemainder
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsRemainder
#check Erdos993Lean.Analytic.V22.Analysis.robbinsRemainder_tendsto_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbinsRemainder_tendsto_zero
#check Erdos993Lean.Analytic.V22.Analysis.robbins_correction_tendsto_zero
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_correction_tendsto_zero
#check Erdos993Lean.Analytic.V22.Analysis.robbins_remainder_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_remainder_bounds
#check Erdos993Lean.Analytic.V22.Analysis.factorial_eq_robbins
#print axioms Erdos993Lean.Analytic.V22.Analysis.factorial_eq_robbins
#check Erdos993Lean.Analytic.V22.Analysis.robbins_factorial_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.robbins_factorial_bounds
