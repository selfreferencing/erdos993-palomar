module

public import Erdos993Lean.Analytic.V22.Analysis.Robbins
public import Erdos993Lean.Analytic.V22.Analysis.WallisUpper
public import Mathlib.Data.Nat.Choose.Cast

/-!
# Version 2.2 of the manuscript, Lemma 3.7: the central-binomial lower bound

The central mass is expressed exactly in terms of the two Robbins remainders,
at `2*m` and `m`. The strict Robbins inequalities imply the stated lower
constant `1/(24*m+1) - 1/(6*m)`; no numerical or finite-check premise is used.
Consumer: the paper's even/odd lower prefactors `L_N`.
This analytic calculation preserves the factorial indices and creates no
forest or process data.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

/-- The exact factorial ratio for the paper's central binomial mass. -/
theorem centralMass_eq_factorial (m : ℕ) :
    centralMass m = ((2 * m).factorial : ℝ) /
      ((m.factorial : ℝ) ^ 2 * (4 : ℝ) ^ m) := by
  unfold centralMass Nat.centralBinom
  rw [Nat.cast_choose ℝ (by omega : m ≤ 2 * m)]
  have hsub : 2 * m - m = m := by omega
  rw [hsub]
  simp only [sq, div_div]

/-- Source: the exact Robbins representation in the proof of note Lemma 3.7. -/
theorem centralMass_eq_robbins {m : ℕ} (hm : 1 ≤ m) :
    centralMass m =
      Real.exp (robbinsRemainder (2 * m) - 2 * robbinsRemainder m) /
        Real.sqrt (Real.pi * (m : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm2 : 1 ≤ 2 * m := by omega
  have hp : ((m : ℝ) / Real.exp 1) ^ m ≠ 0 := by positivity
  have hfour : (4 : ℝ) ^ m ≠ 0 := by positivity
  have he : Real.exp (robbinsRemainder m) ≠ 0 := Real.exp_ne_zero _
  have hs : Real.sqrt (Real.pi * (m : ℝ)) ≠ 0 := by positivity
  have hroot : Real.sqrt (2 * Real.pi * (2 * (m : ℝ))) =
      2 * Real.sqrt (Real.pi * (m : ℝ)) := by
    apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsquare : Real.sqrt (2 * Real.pi * (m : ℝ)) ^ 2 =
      2 * Real.sqrt (Real.pi * (m : ℝ)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
    ring
  have hpower : (2 * (m : ℝ) / Real.exp 1) ^ (2 * m) =
      (4 : ℝ) ^ m * (((m : ℝ) / Real.exp 1) ^ m) ^ 2 := by
    have hbase : 2 * (m : ℝ) / Real.exp 1 = 2 * ((m : ℝ) / Real.exp 1) := by ring
    have htwo : (2 : ℝ) ^ (2 * m) = (4 : ℝ) ^ m := by
      rw [pow_mul]
      norm_num
    rw [hbase, mul_pow, htwo, Nat.mul_comm 2 m, pow_mul]
  have hexp : Real.exp (robbinsRemainder (2 * m) - 2 * robbinsRemainder m) =
      Real.exp (robbinsRemainder (2 * m)) / Real.exp (robbinsRemainder m) ^ 2 := by
    rw [Real.exp_sub, show 2 * robbinsRemainder m =
      robbinsRemainder m + robbinsRemainder m by ring, Real.exp_add]
    ring
  rw [centralMass_eq_factorial, factorial_eq_robbins hm2, factorial_eq_robbins hm]
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [hroot, hpower, hexp]
  simp only [mul_pow]
  rw [hsquare]
  field_simp [hp, hfour, he, hs]
  <;> ring

/-- The strict exponent inequality obtained from the two Robbins remainders. -/
theorem centralMass_robbins_exponent_lower {m : ℕ} (hm : 1 ≤ m) :
    1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ)) <
      robbinsRemainder (2 * m) - 2 * robbinsRemainder m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hlo := (robbins_remainder_bounds (n := 2 * m) (by omega)).1
  have hup := (robbins_remainder_bounds hm).2
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hlo
  have hconst : 2 * (1 / (12 * (m : ℝ))) = 1 / (6 * (m : ℝ)) := by
    field_simp [hm0.ne']
    <;> ring
  have hup2 : 2 * robbinsRemainder m < 1 / (6 * (m : ℝ)) := by
    rw [← hconst]
    exact mul_lt_mul_of_pos_left hup (by norm_num)
  have hlo' : 1 / (24 * (m : ℝ) + 1) < robbinsRemainder (2 * m) := by
    have hden : 12 * (2 * (m : ℝ)) + 1 = 24 * (m : ℝ) + 1 := by ring
    rw [hden] at hlo
    exact hlo
  linarith

/-- The stronger strict lower bound, expressed with an inverse square root. -/
theorem centralMass_lower_sqrt_strict {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ))) *
        (Real.sqrt (Real.pi * (m : ℝ)))⁻¹ < centralMass m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hs : 0 < Real.sqrt (Real.pi * (m : ℝ)) := by positivity
  have h := div_lt_div_of_pos_right
    (Real.exp_lt_exp.mpr (centralMass_robbins_exponent_lower hm)) hs
  rw [← centralMass_eq_robbins hm] at h
  simpa only [div_eq_mul_inv] using h

/-- Source: note Lemma 3.7, the exact lower bound for every `m ≥ 1`. -/
theorem centralMass_lower {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ))) *
        (Real.pi * (m : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ centralMass m := by
  rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  exact (centralMass_lower_sqrt_strict hm).le

/-- Source: note Lemma 3.7, both bounds with their original constants. -/
theorem centralMass_bounds {m : ℕ} (hm : 1 ≤ m) :
    Real.exp (1 / (24 * (m : ℝ) + 1) - 1 / (6 * (m : ℝ))) *
        (Real.pi * (m : ℝ)) ^ (-(1 / 2 : ℝ)) ≤ centralMass m ∧
      centralMass m ≤ (Real.pi * ((m : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) :=
  ⟨centralMass_lower hm, centralMass_upper hm⟩

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.centralMass_eq_factorial
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_eq_factorial
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_eq_robbins
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_eq_robbins
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_robbins_exponent_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_robbins_exponent_lower
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_lower_sqrt_strict
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_lower_sqrt_strict
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_lower
#check Erdos993Lean.Analytic.V22.Analysis.centralMass_bounds
#print axioms Erdos993Lean.Analytic.V22.Analysis.centralMass_bounds
