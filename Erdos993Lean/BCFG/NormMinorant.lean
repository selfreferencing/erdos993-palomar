module

public import Erdos993Lean.BCFG.BernsteinPositivity
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The BCFG packet's activity norm minorant, independent of its exact data.
The finite-data layer supplies the expansion equality; no such equality is an axiom.

-/

@[expose] public section


namespace Erdos993Lean.BCFG

open scoped BigOperators

/-- Powers 1 through N are indexed by i+1, so N=0 has an empty tail. -/
noncomputable def activityCoeff (N : Nat) (A : Nat → Nat → ℝ) (s : ℝ) (j : Nat) : ℝ :=
  A 0 j + ∑ i ∈ Finset.range N, A (i+1) j * s^(i+1)

noncomputable def normLower (N : Nat) (A : Nat → Nat → ℝ) (j : Nat) : ℝ :=
  A 0 j - ∑ i ∈ Finset.range N, |A (i+1) j|

noncomputable def normEval (N M : Nat) (A : Nat → Nat → ℝ) (s z : ℝ) : ℝ :=
  bernsteinSum M (activityCoeff N A s) z

theorem activityCoeff_eq_sum (N : Nat) (A : Nat → Nat → ℝ) (s : ℝ) (j : Nat) :
    activityCoeff N A s j = ∑ i ∈ Finset.range (N+1), A i j * s^i := by
  rw [Finset.sum_range_succ']
  simp [activityCoeff, add_comm]

/-- This is the order of summation printed in the packet. -/
theorem normEval_eq_double_sum (N M : Nat) (A : Nat → Nat → ℝ) (s z : ℝ) :
    normEval N M A s z =
      ∑ i ∈ Finset.range (N+1), ∑ j ∈ Finset.range (M+1),
        (A i j * s^i) * bernsteinBasis M j z := by
  unfold normEval bernsteinSum
  simp_rw [activityCoeff_eq_sum, Finset.sum_mul]
  exact Finset.sum_comm

theorem neg_abs_le_mul_pow (a s : ℝ) (n : Nat) (hs : |s| ≤ 1) :
    -|a| ≤ a * s^n := by
  have hp : |s^n| ≤ 1 := by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg s) hs
  have hm : |a * s^n| ≤ |a| := by
    rw [abs_mul]
    calc
      |a| * |s^n| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg a)
      _ = |a| := mul_one _
  exact (abs_le.mp hm).1

theorem normLower_le_activityCoeff (N : Nat) (A : Nat → Nat → ℝ)
    (s : ℝ) (j : Nat) (hs : |s| ≤ 1) :
    normLower N A j ≤ activityCoeff N A s j := by
  have ht : (∑ i ∈ Finset.range N, -|A (i+1) j|) ≤
      ∑ i ∈ Finset.range N, A (i+1) j * s^(i+1) := by
    apply Finset.sum_le_sum
    intro i hi
    exact neg_abs_le_mul_pow (A (i+1) j) s (i+1) hs
  simp only [Finset.sum_neg_distrib] at ht
  unfold normLower activityCoeff
  linarith

/-- The lower coefficients need not be positive. Only the Bernstein basis
weights are used here; later interval certificates establish positivity. -/
theorem norm_minorant (N M : Nat) (A : Nat → Nat → ℝ) (s z : ℝ)
    (hs : |s| ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    bernsteinSum M (normLower N A) z ≤ normEval N M A s z := by
  unfold normEval bernsteinSum
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_right (normLower_le_activityCoeff N A s j hs)
    (bernsteinBasis_nonneg M j hz)

/-- P is an arbitrary real bivariate evaluation. A checked polynomial expansion
is supplied as hexp, permitting either a Horner-list or Polynomial data layer. -/
theorem activity_norm_minorant
    (P : ℝ → ℝ → ℝ) (N M : Nat) (A : Nat → Nat → ℝ)
    (q a b s z : ℝ)
    (hexp : (1-q)^N * P (q/(1-q)) (a+b*z) = normEval N M A s z)
    (hs : |s| ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    bernsteinSum M (normLower N A) z ≤ (1-q)^N * P (q/(1-q)) (a+b*z) := by
  rw [hexp]
  exact norm_minorant N M A s z hs hz

/-- Strict positivity transfers because the activity normalization is positive.
N=0, M=0 and every endpoint of the s/z domains are included. -/
theorem activity_norm_positive
    (P : ℝ → ℝ → ℝ) (N M : Nat) (A : Nat → Nat → ℝ)
    (q a b s z : ℝ)
    (hq : q < 1)
    (hexp : (1-q)^N * P (q/(1-q)) (a+b*z) = normEval N M A s z)
    (hs : |s| ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1)
    (hlower : 0 < bernsteinSum M (normLower N A) z) :
    0 < P (q/(1-q)) (a+b*z) := by
  have hscaled : 0 < (1-q)^N * P (q/(1-q)) (a+b*z) :=
    lt_of_lt_of_le hlower (activity_norm_minorant P N M A q a b s z hexp hs hz)
  have hfactor : 0 < (1-q)^N := pow_pos (sub_pos.mpr hq) N
  by_contra hp
  have hnonpos : (1-q)^N * P (q/(1-q)) (a+b*z) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfactor.le (le_of_not_gt hp)
  exact (not_lt_of_ge hnonpos) hscaled

/-- Exact rational lower-coefficient calculations can be transported to reals. -/
def rationalNormLower (N : Nat) (A : Nat → Nat → ℚ) (j : Nat) : ℚ :=
  A 0 j - ∑ i ∈ Finset.range N, |A (i+1) j|

theorem rationalNormLower_cast (N : Nat) (A : Nat → Nat → ℚ) (j : Nat) :
    (rationalNormLower N A j : ℝ) =
      normLower N (fun i j => (A i j : ℝ)) j := by
  simp [rationalNormLower, normLower]

end Erdos993Lean.BCFG
