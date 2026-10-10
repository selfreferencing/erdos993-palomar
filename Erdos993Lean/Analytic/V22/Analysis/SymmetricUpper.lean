module

public import Erdos993Lean.Analytic.V22.Analysis.Kernel
public import Erdos993Lean.Analytic.V22.Analysis.WallisUpper
public import Erdos993Lean.Analytic.V22.Analysis.LogShiftBounds

/-!
# Version 2.2 of the manuscript, Lemma 3.8: the symmetric binomial upper bound

The parity-dependent prefactor is exactly the paper's `U_N`. The point mass
uses the project's binomial law extended by zero to every integer index.
The proof retains the atom and its reflection, proves the adjacent-ratio
estimate, and inducts along the right half of the actual binomial row.
Consumer: the activity-one fiber estimate and the tilted upper prefactor.
This is an analytic helper, not a reconstruction of a forest process.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V22.Analysis

open Real Set Erdos993Lean.Analytic.NoValley

/-- Source: note Section 3.3, the exact parity formula for `U_N`. -/
noncomputable def symmetricUpperPrefactor (N : ℕ) : ℝ :=
  if N % 2 = 0 then
    (Real.pi * (((N / 2 : ℕ) : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ))
  else
    Real.exp (1 / (2 * ((N : ℝ) + 1))) *
      (Real.pi * ((((N + 1) / 2 : ℕ) : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ))

theorem symmetricUpperPrefactor_even (m : ℕ) :
    symmetricUpperPrefactor (2 * m) =
      (Real.pi * ((m : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) := by
  unfold symmetricUpperPrefactor
  rw [if_pos (by omega : (2 * m) % 2 = 0)]
  rw [show (2 * m) / 2 = m by omega]

theorem symmetricUpperPrefactor_odd (m : ℕ) :
    symmetricUpperPrefactor (2 * m + 1) =
      Real.exp (1 / (2 * ((2 * m + 1 : ℕ) : ℝ) + 2)) *
        (Real.pi * (((m + 1 : ℕ) : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) := by
  unfold symmetricUpperPrefactor
  rw [if_neg (by omega : (2 * m + 1) % 2 ≠ 0)]
  rw [show (2 * m + 1 + 1) / 2 = m + 1 by omega]
  rw [show 2 * (((2 * m + 1 : ℕ) : ℝ) + 1) =
    2 * ((2 * m + 1 : ℕ) : ℝ) + 2 by ring]

theorem symmetricUpperPrefactor_pos (N : ℕ) : 0 < symmetricUpperPrefactor N := by
  unfold symmetricUpperPrefactor
  split_ifs <;> positivity

/-- The quadratic lower bound paired with the logarithmic lower bound for `1+a`. -/
theorem symmetric_neglog_quadratic_lower {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    a + a ^ 2 / 2 ≤ -Real.log (1 - a) := by
  let f : ℝ → ℝ := fun y => -Real.log (1 - y) - y - y ^ 2 / 2
  have hd : ∀ y ∈ Icc (0 : ℝ) a, HasDerivAt f (y ^ 2 / (1 - y)) y := by
    intro y hy
    have hne : 1 - y ≠ 0 := ne_of_gt (by linarith [hy.2])
    convert (((((hasDerivAt_id y).const_sub 1).log hne).neg).sub
      (hasDerivAt_id y)).sub ((hasDerivAt_pow 2 y).div_const 2) using 1
    · funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply, Pi.neg_apply, id_eq]
      dsimp [f]
    · dsimp [f]
      norm_num
      field_simp [hne]
      ring
  have hc : ContinuousOn f (Icc (0 : ℝ) a) :=
    fun y hy => (hd y hy).continuousAt.continuousWithinAt
  have hm : MonotoneOn f (Icc (0 : ℝ) a) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 a) hc
      (fun y hy => (hd y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => by
        have hy1 : y ≤ a := (interior_subset hy : y ∈ Icc 0 a).2
        exact div_nonneg (sq_nonneg y) (by linarith))
  have h := hm ⟨le_rfl, ha0⟩ ⟨ha0, le_rfl⟩ ha0
  dsimp [f] at h
  norm_num at h
  linarith

/-- Source: note Lemma 3.8, `log ((1-a)/(1+a)) ≤ -2a`. -/
theorem symmetric_log_ratio_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Real.log ((1 - a) / (1 + a)) ≤ -2 * a := by
  rw [Real.log_div (ne_of_gt (by linarith : 0 < 1 - a))
    (ne_of_gt (by linarith : 0 < 1 + a))]
  have hn := symmetric_neglog_quadratic_lower ha0 ha1
  have hp := logShift_log_one_add_lower ha0
  linarith

theorem symmetric_ratio_le_exp {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    (1 - a) / (1 + a) ≤ Real.exp (-2 * a) := by
  have h := Real.exp_le_exp.mpr (symmetric_log_ratio_le ha0 ha1)
  rw [Real.exp_log (div_pos (by linarith : 0 < 1 - a)
    (by linarith : 0 < 1 + a))] at h
  exact h

/-- The symmetric binomial law as a central coefficient over `2^N`. -/
theorem binom_half_nat (N k : ℕ) :
    binom N (1 / 2) (k : ℤ) = (N.choose k : ℝ) / (2 : ℝ) ^ N := by
  by_cases hk : k ≤ N
  · rw [binom_natCast_of_le (1 / 2) hk]
    rw [show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num]
    rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hk]
    simp only [div_eq_mul_inv, one_mul, inv_pow]
  · rw [binom_natCast_of_lt (1 / 2) (by omega), Nat.choose_eq_zero_of_lt (by omega)]
    simp

/-- Same-row adjacent relation, retaining every integer boundary index. -/
theorem binom_half_adjacent {N : ℕ} (hN : 1 ≤ N) (j : ℤ) :
    ((j : ℝ) + 1) * binom N (1 / 2) (j + 1) =
      ((N : ℝ) - j) * binom N (1 / 2) j := by
  have hsucc : N - 1 + 1 = N := Nat.sub_add_cancel hN
  have hcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by exact_mod_cast hsucc
  have hr := binom_step_right (N - 1) (1 / 2) j
  have hl := binom_step_left (N - 1) (1 / 2) (j + 1)
  rw [hsucc, hcast] at hr hl
  rw [add_sub_cancel_right] at hl
  push_cast at hl
  norm_num at hr
  exact hl.symm.trans hr

/-- Source: note Lemma 3.8, reflection of the entire extended binomial row. -/
theorem binom_half_reflect (N : ℕ) (j : ℤ) :
    binom N (1 / 2) ((N : ℤ) - j) = binom N (1 / 2) j := by
  by_cases hj0 : j < 0
  · rw [binom_of_neg hj0, binom_of_gt (by omega : (N : ℤ) < (N : ℤ) - j)]
  by_cases hjN : (N : ℤ) < j
  · rw [binom_of_gt hjN, binom_of_neg (by omega : (N : ℤ) - j < 0)]
  lift j to ℕ using (by omega : 0 ≤ j)
  have hj : j ≤ N := by omega
  have hsub : (N : ℤ) - (j : ℤ) = ((N - j : ℕ) : ℤ) := by omega
  rw [hsub, binom_half_nat, binom_half_nat, Nat.choose_symm hj]

/-- Source: the even central atom in note Lemma 3.8. -/
theorem binom_half_even_center (m : ℕ) :
    binom (2 * m) (1 / 2) (m : ℤ) = centralMass m := by
  rw [binom_half_nat]
  unfold centralMass Nat.centralBinom
  rw [pow_mul]
  norm_num

/-- Source: the odd central atom equals the next even central mass. -/
theorem binom_half_odd_center (m : ℕ) :
    binom (2 * m + 1) (1 / 2) ((m + 1 : ℕ) : ℤ) = centralMass (m + 1) := by
  have h := binom_step_right (2 * m + 1) (1 / 2) ((m + 1 : ℕ) : ℤ)
  rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, binom_half_even_center] at h
  push_cast at h
  have heq : ((m : ℝ) + 1) * binom (2 * m + 1) (1 / 2) ((m + 1 : ℕ) : ℤ) =
      ((m : ℝ) + 1) * centralMass (m + 1) := by
    simp only [Nat.cast_add, Nat.cast_one] at h ⊢
    linear_combination h
  exact mul_left_cancel₀ (by positivity : (m : ℝ) + 1 ≠ 0) heq

/-- The right-half tail estimate before inserting the central-binomial upper bound.
The center `c` may be even or odd; its parity displacement is `2*c-N`. -/
theorem binom_half_right_tail {N c : ℕ} (hN : 1 ≤ N) (hc : (N : ℝ) ≤ 2 * c)
    (d : ℕ) :
    binom N (1 / 2) ((c + d : ℕ) : ℤ) ≤
      binom N (1 / 2) (c : ℤ) *
        Real.exp (-2 * ((d : ℝ) ^ 2 + d * (2 * (c : ℝ) - N)) / ((N : ℝ) + 1)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    by_cases hsupport : c + (d + 1) ≤ N
    · let a : ℝ := (2 * ((c : ℝ) + d) + 1 - N) / ((N : ℝ) + 1)
      have hden : 0 < (N : ℝ) + 1 := by positivity
      have ha0 : 0 ≤ a := by
        dsimp [a]
        apply div_nonneg _ hden.le
        have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
        linarith
      have hsupport' : (c : ℝ) + d + 1 ≤ (N : ℝ) := by exact_mod_cast hsupport
      have ha1 : a < 1 := by
        dsimp [a]
        apply (div_lt_one hden).2
        linarith
      have hratio : ((N : ℝ) - ((c : ℝ) + d)) / ((c : ℝ) + d + 1) ≤
          Real.exp (-2 * a) := by
        have heq : ((N : ℝ) - ((c : ℝ) + d)) / ((c : ℝ) + d + 1) =
            (1 - a) / (1 + a) := by
          have hminus : 1 - a = 2 * ((N : ℝ) - ((c : ℝ) + d)) / ((N : ℝ) + 1) := by
            dsimp [a]
            field_simp [hden.ne']
            ring
          have hplus : 1 + a = 2 * ((c : ℝ) + d + 1) / ((N : ℝ) + 1) := by
            dsimp [a]
            field_simp [hden.ne']
            ring
          rw [hminus, hplus, div_div_div_cancel_right₀ hden.ne',
            mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
        rw [heq]
        exact symmetric_ratio_le_exp ha0 ha1
      have hstep : binom N (1 / 2) ((c + (d + 1) : ℕ) : ℤ) =
          binom N (1 / 2) ((c + d : ℕ) : ℤ) *
            (((N : ℝ) - ((c : ℝ) + d)) / ((c : ℝ) + d + 1)) := by
        have h := binom_half_adjacent hN ((c + d : ℕ) : ℤ)
        have hj : ((c + d : ℕ) : ℤ) + 1 = ((c + (d + 1) : ℕ) : ℤ) := by omega
        rw [hj] at h
        push_cast at h
        rw [← mul_div_assoc]
        apply (eq_div_iff (by positivity : (c : ℝ) + d + 1 ≠ 0)).2
        simp only [Nat.cast_add, Nat.cast_one, Int.cast_add, Int.cast_natCast, add_assoc] at h ⊢
        linear_combination h
      calc
        binom N (1 / 2) ((c + (d + 1) : ℕ) : ℤ) =
            binom N (1 / 2) ((c + d : ℕ) : ℤ) *
              (((N : ℝ) - ((c : ℝ) + d)) / ((c : ℝ) + d + 1)) := hstep
        _ ≤ binom N (1 / 2) ((c + d : ℕ) : ℤ) * Real.exp (-2 * a) :=
          mul_le_mul_of_nonneg_left hratio (binom_nonneg (by norm_num) (by norm_num) _)
        _ ≤ (binom N (1 / 2) (c : ℤ) *
            Real.exp (-2 * ((d : ℝ) ^ 2 + d * (2 * (c : ℝ) - N)) / ((N : ℝ) + 1))) *
              Real.exp (-2 * a) := mul_le_mul_of_nonneg_right ih (Real.exp_nonneg _)
        _ = binom N (1 / 2) (c : ℤ) *
            Real.exp (-2 * (((d + 1 : ℕ) : ℝ) ^ 2 +
              (d + 1 : ℕ) * (2 * (c : ℝ) - N)) / ((N : ℝ) + 1)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          congr 1
          dsimp [a]
          push_cast
          field_simp [hden.ne']
          <;> ring
    · rw [binom_natCast_of_lt (1 / 2) (by omega : N < c + (d + 1))]
      exact mul_nonneg (binom_nonneg (by norm_num) (by norm_num) _) (Real.exp_nonneg _)

/-- Lemma 3.8 on the right half of the row. -/
theorem symmetric_binomial_upper_right {N : ℕ} (hN : 2 ≤ N) (J : ℤ)
    (hhalf : (N : ℝ) / 2 ≤ (J : ℝ)) :
    binom N (1 / 2) J ≤ symmetricUpperPrefactor N *
      Real.exp (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1)) := by
  by_cases heven : N % 2 = 0
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m := ⟨N / 2, by omega⟩
    subst N
    have hm : 1 ≤ m := by omega
    have hj : (m : ℤ) ≤ J := by
      have hjr : (m : ℝ) ≤ (J : ℝ) := by push_cast at hhalf; linarith
      exact_mod_cast hjr
    obtain ⟨d, hJ⟩ : ∃ d : ℕ, J = ((m + d : ℕ) : ℤ) :=
      ⟨(J - (m : ℤ)).toNat, by omega⟩
    subst J
    have ht := binom_half_right_tail (N := 2 * m) (c := m) (by omega)
      (by push_cast; linarith) d
    rw [binom_half_even_center] at ht
    calc
      binom (2 * m) (1 / 2) ((m + d : ℕ) : ℤ) ≤ centralMass m *
          Real.exp (-2 * ((d : ℝ) ^ 2 + d * (2 * (m : ℝ) - (2 * m : ℕ))) /
            (((2 * m : ℕ) : ℝ) + 1)) := ht
      _ ≤ (Real.pi * ((m : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-2 * ((d : ℝ) ^ 2 + d * (2 * (m : ℝ) - (2 * m : ℕ))) /
            (((2 * m : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (centralMass_upper hm) (Real.exp_nonneg _)
      _ = symmetricUpperPrefactor (2 * m) *
          Real.exp (-2 * ((((m + d : ℕ) : ℤ) : ℝ) - ((2 * m : ℕ) : ℝ) / 2) ^ 2 /
            (((2 * m : ℕ) : ℝ) + 1)) := by
        rw [symmetricUpperPrefactor_even]
        congr 1
        congr 1
        push_cast
        ring
  · obtain ⟨m, hform⟩ : ∃ m : ℕ, N = 2 * m + 1 := ⟨N / 2, by omega⟩
    subst N
    have hj2 : 2 * (m : ℤ) + 1 ≤ 2 * J := by
      have hjr : 2 * (m : ℝ) + 1 ≤ 2 * (J : ℝ) := by push_cast at hhalf; linarith
      exact_mod_cast hjr
    have hj : (m : ℤ) + 1 ≤ J := by omega
    obtain ⟨d, hJ⟩ : ∃ d : ℕ, J = ((m + 1 + d : ℕ) : ℤ) :=
      ⟨(J - ((m : ℤ) + 1)).toNat, by omega⟩
    subst J
    have ht := binom_half_right_tail (N := 2 * m + 1) (c := m + 1) (by omega)
      (by push_cast; linarith) d
    rw [binom_half_odd_center] at ht
    have heq : Real.exp (-2 * ((d : ℝ) ^ 2 +
          d * (2 * ((m + 1 : ℕ) : ℝ) - (2 * m + 1 : ℕ))) /
            (((2 * m + 1 : ℕ) : ℝ) + 1)) =
        Real.exp (1 / (2 * ((2 * m + 1 : ℕ) : ℝ) + 2)) *
          Real.exp (-2 * ((((m + 1 + d : ℕ) : ℤ) : ℝ) -
            ((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      field_simp
      <;> ring
    calc
      binom (2 * m + 1) (1 / 2) ((m + 1 + d : ℕ) : ℤ) ≤ centralMass (m + 1) *
          Real.exp (-2 * ((d : ℝ) ^ 2 + d *
            (2 * ((m + 1 : ℕ) : ℝ) - (2 * m + 1 : ℕ))) /
              (((2 * m + 1 : ℕ) : ℝ) + 1)) := ht
      _ ≤ (Real.pi * (((m + 1 : ℕ) : ℝ) + 1 / 4)) ^ (-(1 / 2 : ℝ)) *
          Real.exp (-2 * ((d : ℝ) ^ 2 + d *
            (2 * ((m + 1 : ℕ) : ℝ) - (2 * m + 1 : ℕ))) /
              (((2 * m + 1 : ℕ) : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (centralMass_upper (by omega)) (Real.exp_nonneg _)
      _ = symmetricUpperPrefactor (2 * m + 1) *
          Real.exp (-2 * ((((m + 1 + d : ℕ) : ℤ) : ℝ) -
            ((2 * m + 1 : ℕ) : ℝ) / 2) ^ 2 / (((2 * m + 1 : ℕ) : ℝ) + 1)) := by
        rw [symmetricUpperPrefactor_odd, heq]
        ring

/-- Source: note Lemma 3.8, every integer `J`, including both exterior tails. -/
theorem symmetric_binomial_upper {N : ℕ} (hN : 2 ≤ N) (J : ℤ) :
    binom N (1 / 2) J ≤ symmetricUpperPrefactor N *
      Real.exp (-2 * ((J : ℝ) - (N : ℝ) / 2) ^ 2 / ((N : ℝ) + 1)) := by
  by_cases hhalf : (N : ℝ) / 2 ≤ (J : ℝ)
  · exact symmetric_binomial_upper_right hN J hhalf
  · have href : (N : ℝ) / 2 ≤ (((N : ℤ) - J : ℤ) : ℝ) := by
      push_cast
      linarith
    have h := symmetric_binomial_upper_right hN ((N : ℤ) - J) href
    rw [binom_half_reflect] at h
    have hsq : ((((N : ℤ) - J : ℤ) : ℝ) - (N : ℝ) / 2) ^ 2 =
        ((J : ℝ) - (N : ℝ) / 2) ^ 2 := by push_cast; ring
    simpa only [hsq] using h

end Erdos993Lean.Analytic.V22.Analysis

/-! Defining-module declaration and axiom audit. -/

#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor
#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_even
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_even
#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_odd
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_odd
#check Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_pos
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetricUpperPrefactor_pos
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_neglog_quadratic_lower
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_neglog_quadratic_lower
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_log_ratio_le
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_log_ratio_le
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_ratio_le_exp
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_ratio_le_exp
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_nat
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_nat
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_adjacent
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_adjacent
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_reflect
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_reflect
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_even_center
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_even_center
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_odd_center
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_odd_center
#check Erdos993Lean.Analytic.V22.Analysis.binom_half_right_tail
#print axioms Erdos993Lean.Analytic.V22.Analysis.binom_half_right_tail
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_upper_right
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_upper_right
#check Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_upper
#print axioms Erdos993Lean.Analytic.V22.Analysis.symmetric_binomial_upper
