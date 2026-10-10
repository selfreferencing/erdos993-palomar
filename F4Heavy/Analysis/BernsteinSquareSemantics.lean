module

public import F4Heavy.Analysis.SpecialControlSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

def weightedBernstein (p : List Fraction) (a b : Fraction) (m : Nat) : List Fraction :=
  (bernstein p a b m).zipIdx.map fun (c,j) => Fraction.mul c (Fraction.ofInt (F4Heavy.Finite.choose m j))

theorem weightedBernstein_values (p : List Fraction) (a b : Fraction) (m : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    (weightedBernstein p a b m).map fractionValue =
      (List.range (m+1)).map fun j =>
        fractionValue ((bernstein p a b m)[j]?.getD Fraction.zero)*(m.choose j : ℝ) := by
  apply List.ext_getElem
  · simp [weightedBernstein, bernstein]
  · intro j hj hk
    have hlen : j < (bernstein p a b m).length := by
      simpa only [weightedBernstein, List.length_map, List.length_zipIdx] using hj
    simp only [weightedBernstein, List.getElem_map, List.getElem_zipIdx, Nat.zero_add,
      List.getElem_range, List.getElem?_eq_getElem hlen, Option.getD_some]
    rw [fractionValue_mul _ _
      ((bernstein_den_pos p a b m hp ha hb) _ (List.getElem_mem hlen)) Nat.zero_lt_one,
      fractionValue_ofInt, choose_value]
    norm_cast

theorem weightedBernstein_value (p : List Fraction) (a b : Fraction) (m : Nat) (t : ℝ)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hm : p.length ≤ m+1) (ht : 1-t ≠ 0) :
    realHorner (p.map fractionValue) (fractionValue a+(fractionValue b-fractionValue a)*t) =
      (1-t)^m*realHorner ((weightedBernstein p a b m).map fractionValue) (t/(1-t)) := by
  rw [weightedBernstein_values p a b m hp ha hb, realHorner_map_range, Finset.mul_sum,
    ← bernstein_value p a b m t hp ha hb hm]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bernstein_projective_weight m j t (by have := Finset.mem_range.mp hj; omega) ht]
  ring

theorem bernstein_last_value (p : List Fraction) (a b : Fraction) (m : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hm : p.length ≤ m+1) :
    realHorner (p.map fractionValue) (fractionValue b) =
      fractionValue ((bernstein p a b m)[m]?.getD Fraction.zero) := by
  have h := bernstein_value p a b m 1 hp ha hb hm
  rw [show fractionValue a+(fractionValue b-fractionValue a)*1 = fractionValue b by ring] at h
  rw [← h, Finset.sum_eq_single m]
  · simp [bernsteinWeight]
  · intro j hj hne
    have hjm : j < m := by have := Finset.mem_range.mp hj; omega
    simp [bernsteinWeight, zero_pow (by omega : m-j ≠ 0)]
  · simp

theorem weightedBernstein_last_value (p : List Fraction) (a b : Fraction) (m : Nat)
    (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    fractionValue ((weightedBernstein p a b m)[m]?.getD Fraction.zero) =
      fractionValue ((bernstein p a b m)[m]?.getD Fraction.zero) := by
  have h := congrArg (fun l : List ℝ => l[m]?.getD 0) (weightedBernstein_values p a b m hp ha hb)
  simpa [List.getElem?_map, List.getElem?_eq_getElem,
    show m < (weightedBernstein p a b m).length by simp [weightedBernstein, bernstein]] using h

theorem weightedBernstein_positive_closed (p saved : List Fraction) (a b : Fraction)
    (m : Nat) (x : ℝ) (hp : ∀ c ∈ p, 0 < c.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hm : p.length ≤ m+1) (hab : fractionValue a < fractionValue b)
    (hx0 : fractionValue a ≤ x) (hx1 : x ≤ fractionValue b)
    (heq : Fraction.allEq (weightedBernstein p a b m) saved = true)
    (hpoly : ∀ z : ℝ, 0 ≤ z → 0 < realHorner (saved.map fractionValue) z)
    (hlast : 0 < fractionValue (saved[m]?.getD Fraction.zero)) :
    0 < realHorner (p.map fractionValue) x := by
  have hvals := fraction_allEq_sound _ _ heq
  rcases eq_or_lt_of_le hx1 with rfl | hx1
  · rw [bernstein_last_value p a b m hp ha hb hm,
      ← weightedBernstein_last_value p a b m hp ha hb]
    have he := congrArg (fun l : List ℝ => l[m]?.getD 0) hvals
    have hg : ∀ l : List Fraction, (l.map fractionValue)[m]?.getD 0 =
        fractionValue (l[m]?.getD Fraction.zero) := by
      intro l
      cases h : l[m]? <;> simp [List.getElem?_map, h, fractionValue_zero]
    simp only [hg] at he
    rw [he]
    exact hlast
  · let t := (x-fractionValue a)/(fractionValue b-fractionValue a)
    have hd := sub_pos.mpr hab
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx0) hd.le
    have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith only [hx1])
    have he : fractionValue a+(fractionValue b-fractionValue a)*t = x := by
      dsimp [t]
      field_simp
      <;> ring
    rw [← he, weightedBernstein_value p a b m t hp ha hb hm (ne_of_gt (sub_pos.mpr ht1)), hvals]
    exact mul_pos (pow_pos (sub_pos.mpr ht1) m)
      (hpoly _ (div_nonneg ht0 (sub_pos.mpr ht1).le))

end F4Heavy.Analysis
