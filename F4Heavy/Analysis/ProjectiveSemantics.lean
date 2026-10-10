module

public import F4Heavy.Analysis.ShiftSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite
open scoped BigOperators

theorem projectiveSummand_den_pos (p : List Fraction) (k i : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) :
    0 < (Fraction.mul (p[i]?.getD Fraction.zero)
      (Fraction.ofInt (((-1 : Int)^(k-i)) *
        (F4Heavy.Finite.choose (p.length-1-i) (k-i) : Int)))).den := by
  exact fraction_mul_den_pos _ _ (fractionGet_den_pos p i hp) Nat.zero_lt_one

theorem projectiveSummand_value (p : List Fraction) (k i : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) :
    fractionValue (Fraction.mul (p[i]?.getD Fraction.zero)
      (Fraction.ofInt (((-1 : Int)^(k-i)) *
        (F4Heavy.Finite.choose (p.length-1-i) (k-i) : Int)))) =
      fractionValue (p[i]?.getD Fraction.zero) * (-1 : ℝ)^(k-i) *
        ((p.length-1-i).choose (k-i) : ℝ) := by
  rw [fractionValue_mul _ _ (fractionGet_den_pos p i hp) Nat.zero_lt_one,
    fractionValue_ofInt, choose_value]
  push_cast
  ring

theorem projective_den_pos (p : List Fraction) (hp : ∀ c ∈ p, 0 < c.den) :
    ∀ c ∈ projective p, 0 < c.den := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  apply fraction_sum_den_pos
  intro c hc
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
  exact projectiveSummand_den_pos p k i hp

theorem projective_binomial_sum (n : Nat) (f : Nat → ℝ) (x : ℝ) :
    (∑ k ∈ Finset.range n, (∑ i ∈ Finset.range (k+1),
      f i * (-1 : ℝ)^(k-i) * ((n-1-i).choose (k-i) : ℝ)) * x ^ k) =
      ∑ i ∈ Finset.range n, f i * x ^ i * (1-x)^(n-1-i) := by
  simp only [Finset.sum_mul]
  rw [← triangle_sum_reindex n
    (fun k i => f i * (-1 : ℝ)^(k-i) * ((n-1-i).choose (k-i) : ℝ) * x^k)]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  have hrange : n-i = (n-1-i)+1 := by omega
  rw [hrange, show 1-x = -x+1 by ring, add_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show (-x)^j = (-1 : ℝ)^j * x^j by rw [neg_eq_neg_one_mul x, mul_pow]]
  simp only [Nat.add_sub_cancel, one_pow, mul_one, pow_add]
  ring

theorem projective_value (p : List Fraction) (x : ℝ) (hp : ∀ c ∈ p, 0 < c.den) :
    realHorner ((projective p).map fractionValue) x =
      ∑ i ∈ Finset.range p.length,
        fractionValue (p[i]?.getD Fraction.zero) * x ^ i * (1-x)^(p.length-1-i) := by
  unfold projective
  simp only [List.map_map, Function.comp_def]
  rw [realHorner_map_range]
  apply Eq.trans _ (projective_binomial_sum p.length
    (fun i => fractionValue (p[i]?.getD Fraction.zero)) x)
  apply Finset.sum_congr rfl
  intro k hk
  have hterms : ∀ c ∈ (List.range (k+1)).map (fun i =>
      Fraction.mul (p[i]?.getD Fraction.zero)
        (Fraction.ofInt (((-1 : Int)^(k-i)) *
          (F4Heavy.Finite.choose (p.length-1-i) (k-i) : Int)))), 0 < c.den := by
    intro c hc
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    exact projectiveSummand_den_pos p k i hp
  rw [fractionValue_sum _ hterms]
  simp only [List.map_map, Function.comp_def]
  rw [list_range_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  exact projectiveSummand_value p k i hp

theorem projective_homogenization (p : List Fraction) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (hx : 1-x ≠ 0) :
    realHorner ((projective p).map fractionValue) x =
      (1-x)^(p.length-1) * realHorner (p.map fractionValue) (x/(1-x)) := by
  rw [projective_value p x hp, realHorner_sum_get, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn : i ≤ p.length-1 := by have := Finset.mem_range.mp hi; omega
  rw [div_pow, pow_sub₀ (1-x) hx hn]
  ring

theorem projective_positive_iff (p : List Fraction) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (hx : x < 1) :
    0 < realHorner ((projective p).map fractionValue) x ↔
      0 < realHorner (p.map fractionValue) (x/(1-x)) := by
  have hd : 0 < 1-x := sub_pos.mpr hx
  rw [projective_homogenization p x hp (ne_of_gt hd)]
  exact mul_pos_iff_of_pos_left (pow_pos hd _)

end F4Heavy.Analysis
