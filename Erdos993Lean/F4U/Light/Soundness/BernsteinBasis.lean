module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace F4U.Light
open scoped BigOperators

/-- Unnormalized parent coefficients: the positive factor `choose m s` has
already been included, so the Bernstein basis below has no binomial factor. -/
noncomputable def scaledParentCoefficient (m s : Nat) (a : Nat → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), if j ≤ s then (Nat.choose (m-j) (s-j) : ℝ) * a j else 0

noncomputable def scaledBernsteinSum (m : Nat) (a : Nat → ℝ) (t : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (m+1), a s * t^s * (1-t)^(m-s)

theorem monomial_parent_identity (m j : Nat) (hj : j ≤ m) (t : ℝ) :
    (∑ s ∈ Finset.range (m+1),
      if j ≤ s then (Nat.choose (m-j) (s-j) : ℝ) * t^s * (1-t)^(m-s) else 0) = t^j := by
  have hm : m+1 = j+(m-j+1) := by omega
  rw [hm, Finset.sum_range_add]
  have hz : (∑ s ∈ Finset.range j,
      if j ≤ s then (Nat.choose (m-j) (s-j) : ℝ) * t^s * (1-t)^(m-s) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s hs
    simp [not_le.mpr (Finset.mem_range.mp hs)]
  rw [hz, zero_add]
  have hsum : (∑ k ∈ Finset.range (m-j+1),
      if j ≤ j+k then (Nat.choose (m-j) (j+k-j) : ℝ) * t^(j+k) * (1-t)^(m-(j+k)) else 0) =
      t^j * (∑ k ∈ Finset.range (m-j+1), t^k * (1-t)^(m-j-k) * (Nat.choose (m-j) k : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hsub : m-(j+k) = m-j-k := by omega
    simp only [Nat.le_add_right, ite_true, Nat.add_sub_cancel_left, hsub, pow_add]
    ring
  rw [hsum, ← add_pow]
  simp

theorem scaled_parent_identity (m : Nat) (a : Nat → ℝ) (t : ℝ) :
    scaledBernsteinSum m (scaledParentCoefficient m · a) t =
      ∑ j ∈ Finset.range (m+1), a j * t^j := by
  unfold scaledBernsteinSum scaledParentCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← monomial_parent_identity m j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) t,
      Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  split_ifs <;> ring

theorem scaledBernsteinSum_pos (m : Nat) (a : Nat → ℝ)
    (ha : ∀ s ≤ m, 0 < a s) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    0 < scaledBernsteinSum m a t := by
  unfold scaledBernsteinSum
  have hn : ∀ s ∈ Finset.range (m+1), 0 ≤ a s * t^s * (1-t)^(m-s) := by
    intro s hs
    exact mul_nonneg (mul_nonneg (ha s (Nat.le_of_lt_succ (Finset.mem_range.mp hs))).le
      (pow_nonneg ht.1 _)) (pow_nonneg (sub_nonneg.mpr ht.2) _)
  by_cases h1 : t = 1
  · subst t
    have hp : 0 < a m * (1:ℝ)^m * (1-1)^(m-m) := by simpa using ha m (le_refl m)
    exact lt_of_lt_of_le hp (Finset.single_le_sum hn (Finset.mem_range.mpr (Nat.lt_succ_self m)))
  · have ht1 : t < 1 := lt_of_le_of_ne ht.2 h1
    have hp : 0 < a 0 * t^0 * (1-t)^(m-0) := by
      simpa using mul_pos (ha 0 (Nat.zero_le m)) (pow_pos (sub_pos.mpr ht1) m)
    exact lt_of_lt_of_le hp (Finset.single_le_sum hn (Finset.mem_range.mpr (Nat.succ_pos m)))

theorem powerSum_pos_of_parent (m : Nat) (a : Nat → ℝ)
    (ha : ∀ s ≤ m, 0 < scaledParentCoefficient m s a) {t : ℝ} (ht : 0 ≤ t ∧ t ≤ 1) :
    0 < ∑ j ∈ Finset.range (m+1), a j * t^j := by
  rw [← scaled_parent_identity]
  exact scaledBernsteinSum_pos m _ ha ht

end F4U.Light
