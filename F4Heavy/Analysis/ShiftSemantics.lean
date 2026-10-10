module

public import F4Heavy.Analysis.TransformBasics
public import Mathlib.Data.Nat.Choose.Sum

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite
open scoped BigOperators

theorem list_range_sum (n : Nat) (f : Nat → ℝ) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem realHorner_map_range (n : Nat) (f : Nat → ℝ) (x : ℝ) :
    realHorner ((List.range n).map f) x = ∑ k ∈ Finset.range n, f k * x ^ k := by
  induction n generalizing f with
  | zero => simp [realHorner]
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, realHorner_cons, Function.comp_def]
    rw [ih, Finset.sum_range_succ']
    simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
    simp only [Nat.succ_eq_add_one, Nat.add_comm]
    ring_nf

theorem fractionGet_den_pos (p : List Fraction) (i : Nat) (hp : ∀ a ∈ p, 0 < a.den) :
    0 < (p[i]?.getD Fraction.zero).den := by
  by_cases hi : i < p.length
  · rw [List.getElem?_eq_getElem hi]
    exact hp _ (List.getElem_mem hi)
  · rw [List.getElem?_eq_none (by omega)]
    exact Nat.zero_lt_one

theorem realHorner_sum_get (p : List Fraction) (x : ℝ) :
    realHorner (p.map fractionValue) x =
      ∑ i ∈ Finset.range p.length, fractionValue (p[i]?.getD Fraction.zero) * x ^ i := by
  have hmap : (List.range p.length).map (fun i => fractionValue (p[i]?.getD Fraction.zero)) =
      p.map fractionValue := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.length_map, List.length_range] at h1
      simp [List.getElem?_eq_getElem h1]
  rw [← hmap]
  exact realHorner_map_range _ _ x

theorem triangle_sum_reindex (n : Nat) (f : Nat → Nat → ℝ) :
    (∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n - k), f (j + k) k) =
      ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (i + 1), f i k := by
  have h := Finset.sum_Ico_Ico_comm 0 n (fun k i => f i k)
  simpa only [Nat.Ico_zero_eq_range, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using h

theorem binomial_shift_sum (n : Nat) (f : Nat → ℝ) (a b x : ℝ) :
    (∑ k ∈ Finset.range n, b ^ k *
      (∑ j ∈ Finset.range (n - k), f (j + k) * ((j + k).choose k : ℝ) * a ^ j) * x ^ k) =
      ∑ i ∈ Finset.range n, f i * (a + b * x) ^ i := by
  have h := triangle_sum_reindex n
    (fun i k => f i * (i.choose k : ℝ) * a ^ (i - k) * (b * x) ^ k)
  calc
    _ = ∑ k ∈ Finset.range n, ∑ j ∈ Finset.range (n - k),
        f (j + k) * ((j + k).choose k : ℝ) * a ^ (j + k - k) * (b * x) ^ k := by
      simp only [Finset.mul_sum, Finset.sum_mul, Nat.add_sub_cancel, mul_pow]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [add_comm a, add_pow, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

theorem shiftSummand_den_pos (p : List Fraction) (a : Fraction) (j k : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) :
    0 < (Fraction.mul (p[j+k]?.getD Fraction.zero)
      (Fraction.mul (Fraction.ofInt (F4Heavy.Finite.choose (j+k) k))
        (Fraction.pow a (j+k-k)))).den := by
  exact fraction_mul_den_pos _ _ (fractionGet_den_pos p _ hp)
    (fraction_mul_den_pos _ _ Nat.zero_lt_one (pow_pos ha _))

theorem shiftSummand_value (p : List Fraction) (a : Fraction) (j k : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) :
    fractionValue (Fraction.mul (p[j+k]?.getD Fraction.zero)
      (Fraction.mul (Fraction.ofInt (F4Heavy.Finite.choose (j+k) k))
        (Fraction.pow a (j+k-k)))) =
    fractionValue (p[j+k]?.getD Fraction.zero) * ((j+k).choose k : ℝ) * fractionValue a ^ j := by
  rw [fractionValue_mul _ _ (fractionGet_den_pos p _ hp)
    (fraction_mul_den_pos _ _ Nat.zero_lt_one (pow_pos ha _)),
    fractionValue_mul _ _ Nat.zero_lt_one (pow_pos ha _),
    fractionValue_ofInt, fractionValue_pow, choose_value, Nat.add_sub_cancel]
  push_cast
  ring

theorem shifted_den_pos (p : List Fraction) (a b : Fraction)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    ∀ c ∈ shifted p a b, 0 < c.den := by
  intro c hc
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hc
  apply fraction_mul_den_pos _ _ (pow_pos hb _)
  apply fraction_sum_den_pos
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  exact shiftSummand_den_pos p a j k hp ha

theorem shifted_value (p : List Fraction) (a b : Fraction) (x : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    realHorner ((shifted p a b).map fractionValue) x =
      realHorner (p.map fractionValue) (fractionValue a + fractionValue b * x) := by
  unfold shifted
  simp only [List.map_map, Function.comp_def]
  rw [realHorner_map_range, realHorner_sum_get]
  apply Eq.trans _ (binomial_shift_sum p.length
    (fun i => fractionValue (p[i]?.getD Fraction.zero)) (fractionValue a) (fractionValue b) x)
  apply Finset.sum_congr rfl
  intro k hk
  have hterms : ∀ c ∈ (List.range (p.length-k)).map (fun j =>
      Fraction.mul (p[j+k]?.getD Fraction.zero)
        (Fraction.mul (Fraction.ofInt (F4Heavy.Finite.choose (j+k) k))
          (Fraction.pow a (j+k-k)))), 0 < c.den := by
    intro c hc
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
    exact shiftSummand_den_pos p a j k hp ha
  rw [fractionValue_mul _ _ (pow_pos hb _) (fraction_sum_den_pos _ hterms),
    fractionValue_pow, fractionValue_sum _ hterms]
  simp only [List.map_map, Function.comp_def]
  rw [list_range_sum]
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  exact shiftSummand_value p a j k hp ha

end F4Heavy.Analysis
