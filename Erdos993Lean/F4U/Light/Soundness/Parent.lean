module

public import Erdos993Lean.F4U.Light.Soundness.Polynomial
public import Erdos993Lean.F4U.Light.Soundness.BernsteinBasis

@[expose] public section


namespace F4U.Light
open scoped BigOperators

theorem eval_parentGo (m s j : Nat) (rows : List (List Int)) (acc : List Int) (x : ℝ) :
    eval (parentGo m s j rows acc) x = eval acc x +
      ∑ k ∈ Finset.range rows.length,
        if j + k ≤ s then (Nat.choose (m - (j + k)) (s - (j + k)) : ℝ) *
          eval (rows.getD k []) x else 0 := by
  induction rows generalizing j acc with
  | nil => simp [parentGo]
  | cons r rows ih =>
    by_cases hj : j ≤ s
    · rw [parentGo, if_pos hj, ih]
      simp only [eval_padd, eval_pscale, Int.ofNat_eq_natCast, Int.cast_natCast, binom_eq_choose,
        List.length_cons, Finset.sum_range_succ', List.getD_cons_zero, Nat.add_zero,
        if_pos hj, List.getD_cons_succ]
      have he : (∑ k ∈ Finset.range rows.length,
          if j + 1 + k ≤ s then (Nat.choose (m - (j + 1 + k)) (s - (j + 1 + k)) : ℝ) *
            eval (rows.getD k []) x else 0) =
          ∑ k ∈ Finset.range rows.length,
          if j + (k + 1) ≤ s then (Nat.choose (m - (j + (k + 1))) (s - (j + (k + 1))) : ℝ) *
            eval (rows.getD k []) x else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have h : j + 1 + k = j + (k + 1) := by omega
        rw [h]
      rw [he]
      ring
    · rw [parentGo, if_neg hj]
      have hz : (∑ k ∈ Finset.range (r :: rows).length,
          if j + k ≤ s then (Nat.choose (m - (j + k)) (s - (j + k)) : ℝ) *
            eval ((r :: rows).getD k []) x else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [if_neg (by omega : ¬ j + k ≤ s)]
      rw [hz, add_zero]

/-- Parent control construction preserves the padded primitive numerator rows verbatim. -/
theorem eval_parent (m s : Nat) (rows : List (List Int)) (hlen : rows.length ≤ m + 1)
    (x : ℝ) : eval (parent m s rows) x =
      scaledParentCoefficient m s (fun j => eval (rows.getD j []) x) := by
  rw [parent, eval_parentGo]
  simp only [eval_nil, zero_add, Nat.zero_add, scaledParentCoefficient]
  apply Finset.sum_subset (Finset.range_mono hlen)
  intro j hj hjnot
  have hjlen : rows.length ≤ j := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hjnot)
  have hr : rows.getD j [] = [] := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hjlen]
  rw [hr]
  simp

/-- The manuscript's parent Bernstein coefficient, with the usual binomial ratios. -/
noncomputable def parentBernsteinCoefficient (m s : Nat) (a : Nat → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    if j ≤ s then a j * (s.choose j : ℝ) / (m.choose j : ℝ) else 0

theorem scaledParentCoefficient_eq (m s : Nat) (hs : s ≤ m) (a : Nat → ℝ) :
    scaledParentCoefficient m s a = (m.choose s : ℝ) * parentBernsteinCoefficient m s a := by
  unfold scaledParentCoefficient parentBernsteinCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hjs : j ≤ s
  · simp only [hjs, ite_true]
    have hjm : j ≤ m := le_trans hjs hs
    have hn : (m.choose j : ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hjm
    have he : (m.choose s : ℝ) * (s.choose j : ℝ) =
        (m.choose j : ℝ) * ((m - j).choose (s - j) : ℝ) := by
      exact_mod_cast Nat.choose_mul hjs
    rw [← mul_div_assoc]
    apply (eq_div_iff hn).mpr
    nlinarith [congrArg (fun z : ℝ => z * a j) he]
  · simp [hjs]

theorem parentBernsteinCoefficient_pos_of_scaled {m s : Nat} (hs : s ≤ m) (a : Nat → ℝ)
    (h : 0 < scaledParentCoefficient m s a) : 0 < parentBernsteinCoefficient m s a := by
  rw [scaledParentCoefficient_eq m s hs a] at h
  have hp : (0 : ℝ) < m.choose s := by exact_mod_cast Nat.choose_pos hs
  exact (mul_pos_iff_of_pos_left hp).mp h

end F4U.Light
