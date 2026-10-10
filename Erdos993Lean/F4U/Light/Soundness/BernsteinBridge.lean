module
public import Erdos993Lean.F4U.Light.Soundness.Polynomial
public import Erdos993Lean.F4U.Light.Soundness.BernsteinBasis
public import Mathlib.Data.List.GetD

@[expose] public section

namespace F4U.Light
open scoped BigOperators

theorem eval_eq_sum (G : List Int) (u : ℝ) :
    eval G u = ∑ j ∈ Finset.range G.length, (G.getD j 0 : ℝ) * u^j := by
  induction G with
  | nil => simp
  | cons a G ih =>
    rw [eval_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, pow_zero, mul_one, pow_succ]
    rw [Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem eval_eq_sum_padded (G : List Int) (n : Nat) (hn : G.length ≤ n) (u : ℝ) :
    eval G u = ∑ j ∈ Finset.range n, (G.getD j 0 : ℝ) * u^j := by
  rw [eval_eq_sum]
  apply Finset.sum_subset (Finset.range_mono hn)
  intro j hj hnot
  have hlen : G.length ≤ j := Nat.le_of_not_gt (fun h => hnot (Finset.mem_range.mpr h))
  rw [List.getD_eq_default G 0 hlen]
  simp

theorem bernGo_eq_sum (n s k : Nat) (G : List Int) :
    bernGo n s k G = ∑ i ∈ Finset.range G.length,
      if k+i ≤ s then Int.ofNat (Nat.choose (n-(k+i)) (s-(k+i))) * G.getD i 0 else 0 := by
  induction G generalizing k with
  | nil => simp [bernGo]
  | cons a G ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.add_zero]
    by_cases h : k ≤ s
    · simp only [bernGo, h, ite_true, binom_eq_choose, ih]
      conv_rhs => rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Nat.add_assoc, Nat.add_comm 1 i]
    · simp only [bernGo, h, ite_false, add_zero]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      simp [show ¬ k+(i+1) ≤ s by omega]

theorem bernGo_eq_scaledParent (n s : Nat) (G : List Int) (hn : G.length = n+1) :
    (bernGo n s 0 G : ℝ) = scaledParentCoefficient n s (fun j => (G.getD j 0 : ℝ)) := by
  rw [bernGo_eq_sum, hn]
  unfold scaledParentCoefficient
  rw [Int.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j ≤ s <;> simp [h]

theorem bernAll_sound {n k : Nat} {G : List Int} (h : bernAll n G k = true) :
    ∀ j ≤ k, 0 < bernGo n j 0 G := by
  induction k with
  | zero =>
    intro j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact of_decide_eq_true h
  | succ k ih =>
    have hh := Bool.and_eq_true_iff.mp h
    intro j hj
    by_cases hjk : j ≤ k
    · exact ih hh.2 j hjk
    · have hj1 : j = k+1 := by omega
      subst j
      exact of_decide_eq_true hh.1

/-- The exceptional rule proves strict positivity on the full closed interval.
All scaled Bernstein coefficients, including both endpoint coefficients, pass. -/
theorem bernOK_sound {G : List Int} (h : bernOK G = true) {u : ℝ}
    (hu : 0 ≤ u ∧ u ≤ 1) : 0 < eval G u := by
  cases G with
  | nil => simp [bernOK, bernAll, bernGo] at h
  | cons a G =>
    let n := (a::G).length-1
    have hn : (a::G).length = n+1 := by simp [n]
    rw [eval_eq_sum_padded (a::G) (n+1) (by omega)]
    apply powerSum_pos_of_parent n _ _ hu
    intro s hs
    rw [← bernGo_eq_scaledParent n s (a::G) hn]
    have hp : 0 < bernGo n s 0 (a::G) := bernAll_sound h s hs
    exact_mod_cast hp

end F4U.Light
