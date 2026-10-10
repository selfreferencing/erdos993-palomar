module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

/-!
General Bernstein positivity for the BCFG packet.
No packet-specific numbers or expansion identities are assumed as axioms.

-/

@[expose] public section


namespace Erdos993Lean.BCFG

open scoped BigOperators Polynomial

noncomputable def bernsteinBasis (M j : Nat) (z : ℝ) : ℝ :=
  (M.choose j : ℝ) * z^j * (1-z)^(M-j)

noncomputable def bernsteinSum (M : Nat) (c : Nat → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (M+1), c j * bernsteinBasis M j z

theorem bernsteinBasis_nonneg (M j : Nat) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ bernsteinBasis M j z := by
  unfold bernsteinBasis
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz.1 _))
    (pow_nonneg (sub_nonneg.mpr hz.2) _)

theorem bernsteinSum_nonneg (M : Nat) (c : Nat → ℝ)
    (hc : ∀ j ≤ M, 0 ≤ c j) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 ≤ bernsteinSum M c z := by
  unfold bernsteinSum
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (hc j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
    (bernsteinBasis_nonneg M j hz)

/-- Strict positivity holds on the closed interval, including M=0.
At z=1 the last basis term is positive; elsewhere the first term is positive. -/
theorem bernsteinSum_pos (M : Nat) (c : Nat → ℝ)
    (hc : ∀ j ≤ M, 0 < c j) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 < bernsteinSum M c z := by
  have hn : ∀ j ∈ Finset.range (M+1), 0 ≤ c j * bernsteinBasis M j z := by
    intro j hj
    exact mul_nonneg (le_of_lt (hc j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))))
      (bernsteinBasis_nonneg M j hz)
  by_cases h1 : z = 1
  · subst z
    have ht : 0 < c M * bernsteinBasis M M 1 := by
      simpa [bernsteinBasis] using hc M (le_refl M)
    exact lt_of_lt_of_le ht
      (Finset.single_le_sum hn (Finset.mem_range.mpr (Nat.lt_succ_self M)))
  · have hz1 : z < 1 := lt_of_le_of_ne hz.2 h1
    have ht : 0 < c 0 * bernsteinBasis M 0 z := by
      simpa [bernsteinBasis] using
        mul_pos (hc 0 (Nat.zero_le M)) (pow_pos (sub_pos.mpr hz1) M)
    exact lt_of_lt_of_le ht
      (Finset.single_le_sum hn (Finset.mem_range.mpr (Nat.succ_pos M)))

/-- Matches the packet's exact polynomial identity interface on any interval. -/
theorem positive_on_interval_of_bernstein
    (f : ℝ → ℝ) (M : Nat) (c : Nat → ℝ) (a b : ℝ)
    (hab : a < b)
    (hrep : ∀ t : ℝ, f (a+(b-a)*t) = bernsteinSum M c t)
    (hc : ∀ j ≤ M, 0 < c j) {x : ℝ} (hx : a ≤ x ∧ x ≤ b) :
    0 < f x := by
  let t := (x-a)/(b-a)
  have hd : 0 < b-a := sub_pos.mpr hab
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx.1) (le_of_lt hd)
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hxt : a+(b-a)*t = x := by
    dsimp [t]
    field_simp [ne_of_gt hd] <;> ring
  rw [← hxt, hrep]
  exact bernsteinSum_pos M c hc ⟨ht0,ht1⟩

/-- Standard Mathlib polynomial basis, so exact Rat polynomial equalities can
be checked independently of the real positivity proof. -/
noncomputable def rationalBernsteinPolynomial (M : Nat) (c : Nat → ℚ) : ℚ[X] :=
  ∑ j ∈ Finset.range (M+1), Polynomial.C (c j) * bernsteinPolynomial ℚ M j

theorem eval_rationalBernsteinPolynomial (M : Nat) (c : Nat → ℚ) (z : ℝ) :
    ((rationalBernsteinPolynomial M c).map (algebraMap ℚ ℝ)).eval z =
      bernsteinSum M (fun j => (c j : ℝ)) z := by
  simp [rationalBernsteinPolynomial, bernsteinSum, bernsteinBasis, bernsteinPolynomial]

theorem rational_polynomial_pos_of_bernstein
    (P : ℚ[X]) (M : Nat) (c : Nat → ℚ)
    (hrep : P = rationalBernsteinPolynomial M c)
    (hc : ∀ j ≤ M, (0 : ℚ) < c j) {z : ℝ} (hz : 0 ≤ z ∧ z ≤ 1) :
    0 < (P.map (algebraMap ℚ ℝ)).eval z := by
  rw [hrep, eval_rationalBernsteinPolynomial]
  apply bernsteinSum_pos M _ (fun j hj => ?_) hz
  exact_mod_cast hc j hj

/-- Finite data may use a list or an array through this Nat-indexed interface.
A missing entry filled by zero cannot pass this strict positivity check. -/
def positiveCoefficients (M : Nat) (c : Nat → ℚ) : Bool :=
  (List.range (M+1)).all (fun j => decide ((0 : ℚ) < c j))

theorem positiveCoefficients_sound {M : Nat} {c : Nat → ℚ}
    (h : positiveCoefficients M c = true) :
    ∀ j ≤ M, (0 : ℚ) < c j := by
  intro j hj
  unfold positiveCoefficients at h
  exact of_decide_eq_true (List.all_eq_true.mp h j
    (List.mem_range.mpr (Nat.lt_succ_iff.mpr hj)))

end Erdos993Lean.BCFG
