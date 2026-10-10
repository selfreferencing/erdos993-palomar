module

public import Erdos993Lean.IndependencePoly
public import Erdos993Lean.Ceiling.HardCore

/-!
The finite-forest conventions in version 2.13 of the manuscript, Section2, source r12:sec1.1
and r12:sec1.2. Counts are extended by zero to negative integer ranks.
The empty forest is included. No mode inequality is assumed here.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

open Finset Polynomial

attribute [local instance] Classical.propDecidable

/-- The printed I(F;x), with integer coefficients. -/
noncomputable def forestPoly (F : FiniteForest) : ℤ[X] := by
  classical
  exact indepPoly F.graph univ

/-- The printed i_k, extended by zero at negative ranks. -/
noncomputable def coefficient (F : FiniteForest) (k : ℤ) : ℕ :=
  if 0 ≤ k then independenceCount F k.toNat else 0

/-- The literal open window ⌈n/4⌉ < k < h_B on integer ranks. -/
noncomputable def WindowRank (F : FiniteForest) (k : ℤ) : Prop :=
  (((F.n + 3) / 4 : ℕ) : ℤ) < k ∧ k < (hB F : ℤ)

/-- A weak valley, including equalities, at a positive integer rank. -/
noncomputable def CoefficientValley (F : FiniteForest) (k : ℤ) : Prop :=
  1 ≤ k ∧ coefficient F k ≤ coefficient F (k - 1) ∧
    coefficient F k ≤ coefficient F (k + 1)

theorem count_eq_indepCount (F : FiniteForest) (k : ℕ) :
    independenceCount F k = indepCount F.graph univ k := by
  classical
  exact (indepCount_univ F.graph k).symm

theorem forestPoly_coeff (F : FiniteForest) (k : ℕ) :
    (forestPoly F).coeff k = (independenceCount F k : ℤ) := by
  classical
  simpa only [forestPoly, count_eq_indepCount] using indepPoly_coeff F.graph univ k

theorem count_zero (F : FiniteForest) : independenceCount F 0 = 1 := by
  classical
  rw [count_eq_indepCount]
  exact indepCount_zero F.graph univ

theorem count_eq_zero_above_order (F : FiniteForest) {k : ℕ} (hk : F.n < k) :
    independenceCount F k = 0 := by
  classical
  rw [count_eq_indepCount]
  apply indepCount_eq_zero_of_card_lt
  simpa using hk

theorem count_finite_support (F : FiniteForest) :
    ∀ k : ℕ, F.n + 1 ≤ k → independenceCount F k = 0 := by
  intro k hk
  exact count_eq_zero_above_order F (by omega)

theorem coefficient_nat (F : FiniteForest) (k : ℕ) :
    coefficient F (k : ℤ) = independenceCount F k := by
  simp [coefficient]

theorem coefficient_negative (F : FiniteForest) {k : ℤ} (hk : k < 0) :
    coefficient F k = 0 := by
  simp [coefficient, not_le.mpr hk]

theorem coefficient_finite_support (F : FiniteForest) {k : ℤ} (hk : (F.n : ℤ) < k) :
    coefficient F k = 0 := by
  have hk0 : 0 ≤ k := by omega
  rw [coefficient, if_pos hk0]
  apply count_eq_zero_above_order
  omega

theorem forestPoly_empty (F : FiniteForest) (hn : F.n = 0) : forestPoly F = 1 := by
  classical
  have hu : (univ : Finset (Fin F.n)) = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro v _
    have hv := v.isLt
    omega
  simpa only [forestPoly, hu] using indepPoly_empty F.graph

theorem count_empty (F : FiniteForest) (hn : F.n = 0) (k : ℕ) :
    independenceCount F k = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · simp [hk, count_zero]
  · have h : F.n < k := by omega
    simp [hk, count_eq_zero_above_order F h]

/-- The coefficient normalization is valid at every nonnegative activity. -/
theorem partitionFn_pos (F : FiniteForest) {t : ℝ} (ht : 0 ≤ t) : 0 < partitionFn F t := by
  have h0 : 0 ∈ range (F.n + 1) := by simp
  have hsum := Finset.single_le_sum
    (s := range (F.n + 1)) (f := fun k => (independenceCount F k : ℝ) * t ^ k)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht _)) h0
  have hs : (1 : ℝ) ≤ partitionFn F t := by
    simpa only [count_zero, Nat.cast_one, pow_zero, one_mul, partitionFn] using hsum
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hs

theorem normalized_coefficients_sum (F : FiniteForest) {t : ℝ} (ht : 0 ≤ t) :
    (∑ k ∈ range (F.n + 1),
      (independenceCount F k : ℝ) * t ^ k / partitionFn F t) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (partitionFn_pos F ht).ne'

theorem partitionFn_empty (F : FiniteForest) (hn : F.n = 0) (t : ℝ) :
    partitionFn F t = 1 := by
  simp [partitionFn, hn, count_zero]

theorem hardCoreMean_empty (F : FiniteForest) (hn : F.n = 0) (t : ℝ) :
    hardCoreMean F t = 0 := by
  simp [hardCoreMean, hn]

/-- This is the real-ceiling spelling of the paper's open window. -/
theorem windowRank_iff_ceiling (F : FiniteForest) (k : ℤ) :
    WindowRank F k ↔ Int.ceil ((F.n : ℝ) / 4) < k ∧ k < (hB F : ℤ) := by
  have hc : Int.ceil ((F.n : ℝ) / 4) = (((F.n + 3) / 4 : ℕ) : ℤ) := by
    apply Int.ceil_eq_iff.mpr
    constructor
    · have h : (((F.n + 3) / 4 : ℕ) : ℤ) * 4 < (F.n : ℤ) + 4 := by omega
      have hr : (((F.n + 3) / 4 : ℕ) : ℝ) * 4 < (F.n : ℝ) + 4 := by exact_mod_cast h
      simp only [Int.cast_natCast]
      linarith
    · have h : F.n ≤ ((F.n + 3) / 4) * 4 := by omega
      have hr : (F.n : ℝ) ≤ (((F.n + 3) / 4 : ℕ) : ℝ) * 4 := by exact_mod_cast h
      simp only [Int.cast_natCast]
      linarith
  simp only [WindowRank, hc]

end Erdos993Lean.Analytic.V213

#check Erdos993Lean.Analytic.V213.count_eq_indepCount
#print axioms Erdos993Lean.Analytic.V213.count_eq_indepCount

#check Erdos993Lean.Analytic.V213.forestPoly_coeff
#print axioms Erdos993Lean.Analytic.V213.forestPoly_coeff

#check Erdos993Lean.Analytic.V213.count_zero
#print axioms Erdos993Lean.Analytic.V213.count_zero

#check Erdos993Lean.Analytic.V213.count_eq_zero_above_order
#print axioms Erdos993Lean.Analytic.V213.count_eq_zero_above_order

#check Erdos993Lean.Analytic.V213.count_finite_support
#print axioms Erdos993Lean.Analytic.V213.count_finite_support

#check Erdos993Lean.Analytic.V213.coefficient_nat
#print axioms Erdos993Lean.Analytic.V213.coefficient_nat

#check Erdos993Lean.Analytic.V213.coefficient_negative
#print axioms Erdos993Lean.Analytic.V213.coefficient_negative

#check Erdos993Lean.Analytic.V213.coefficient_finite_support
#print axioms Erdos993Lean.Analytic.V213.coefficient_finite_support

#check Erdos993Lean.Analytic.V213.forestPoly_empty
#print axioms Erdos993Lean.Analytic.V213.forestPoly_empty

#check Erdos993Lean.Analytic.V213.count_empty
#print axioms Erdos993Lean.Analytic.V213.count_empty

#check Erdos993Lean.Analytic.V213.partitionFn_pos
#print axioms Erdos993Lean.Analytic.V213.partitionFn_pos

#check Erdos993Lean.Analytic.V213.normalized_coefficients_sum
#print axioms Erdos993Lean.Analytic.V213.normalized_coefficients_sum

#check Erdos993Lean.Analytic.V213.partitionFn_empty
#print axioms Erdos993Lean.Analytic.V213.partitionFn_empty

#check Erdos993Lean.Analytic.V213.hardCoreMean_empty
#print axioms Erdos993Lean.Analytic.V213.hardCoreMean_empty

#check Erdos993Lean.Analytic.V213.windowRank_iff_ceiling
#print axioms Erdos993Lean.Analytic.V213.windowRank_iff_ceiling
