module

public import F4Heavy.Analysis.ParametricSquareSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def activityControlPolynomial (p : List (List Fraction)) (a b : Fraction) (n m i : Nat) :
    List Fraction :=
  (List.range (m+1)).map fun j => (bernstein (column p j) a b n)[i]?.getD Fraction.zero

theorem activityControlPolynomial_den_pos (p : List (List Fraction)) (a b : Fraction) (n m i : Nat)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    ∀ c ∈ activityControlPolynomial p a b n m i, 0 < c.den := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hc
  exact fractionGet_den_pos _ i (bernstein_den_pos _ a b n (column_den_pos p j hp) ha hb)

theorem activityControlPolynomial_value (p : List (List Fraction)) (a b : Fraction)
    (n m : Nat) (t x : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (ha : 0 < a.den) (hb : 0 < b.den) (hn : p.length ≤ n+1)
    (hm : ∀ row ∈ p, row.length ≤ m+1) :
    matrixValue p (fractionValue a+(fractionValue b-fractionValue a)*t) x =
      ∑ i ∈ Finset.range (n+1), bernsteinWeight n i t *
        realHorner ((activityControlPolynomial p a b n m i).map fractionValue) x := by
  rw [matrixValue_transpose p (m+1) _ x hm]
  have he : ∀ j, realHorner ((column p j).map fractionValue)
      (fractionValue a+(fractionValue b-fractionValue a)*t) =
      ∑ i ∈ Finset.range (n+1), bernsteinWeight n i t *
        fractionValue ((bernstein (column p j) a b n)[i]?.getD Fraction.zero) := by
    intro j
    simpa only [mul_comm] using (bernstein_value (column p j) a b n t
      (column_den_pos p j hp) ha hb (by simpa only [column, List.length_map] using hn)).symm
  simp_rw [he]
  rw [realHorner_map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [activityControlPolynomial, List.map_map, Function.comp_def] using
    realHorner_map_scale ((List.range (m+1)).map fun j =>
      fractionValue ((bernstein (column p j) a b n)[i]?.getD Fraction.zero)) (bernsteinWeight n i t) x

theorem activityControlPolynomial_rectangle_positive (p : List (List Fraction)) (a b : Fraction)
    (n m : Nat) (v x : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (ha : 0 < a.den) (hb : 0 < b.den) (hn : p.length ≤ n+1)
    (hm : ∀ row ∈ p, row.length ≤ m+1) (hab : fractionValue a < fractionValue b)
    (hv0 : fractionValue a ≤ v) (hv1 : v ≤ fractionValue b)
    (hcontrols : ∀ i ≤ n, 0 < realHorner ((activityControlPolynomial p a b n m i).map fractionValue) x) :
    0 < matrixValue p v x := by
  let t := (v-fractionValue a)/(fractionValue b-fractionValue a)
  have hd := sub_pos.mpr hab
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hv0) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith only [hv1])
  have heq : fractionValue a+(fractionValue b-fractionValue a)*t = v := by
    dsimp [t]
    field_simp
    <;> ring
  rw [← heq, activityControlPolynomial_value p a b n m t x hp ha hb hn hm]
  simpa only [mul_comm] using bernstein_positive_combination n
    (fun i => realHorner ((activityControlPolynomial p a b n m i).map fractionValue) x)
    t ht0 ht1 hcontrols

end F4Heavy.Analysis
