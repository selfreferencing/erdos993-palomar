module

public import F4Heavy.Analysis.MatrixSemantics
public import F4Heavy.Analysis.QuadraticCheck

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem ordinaryControl_centered_value (p : List (List Fraction)) (xl a b : Fraction)
    (m j : Nat) (v : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (hl : 0 < xl.den) (ha : 0 < a.den) (hb : 0 < b.den) :
    realHorner ((ordinaryControl p xl m j a b false false).map fractionValue)
      (v-(fractionValue a+fractionValue b)/2) =
      realHorner ((column (parentColumns p xl m) j).map fractionValue) v := by
  have hc := column_den_pos (parentColumns p xl m) j (parentColumns_den_pos p xl m hp hl)
  have hd := fraction_div_den_pos (Fraction.add a b) (Fraction.ofInt 2)
    (fraction_add_den_pos a b ha hb) (by norm_num [Fraction.ofInt])
  have hv : fractionValue (Fraction.div (Fraction.add a b) (Fraction.ofInt 2)) =
      (fractionValue a+fractionValue b)/2 := by
    rw [fractionValue_div _ _ (fraction_add_den_pos a b ha hb) (by norm_num [Fraction.ofInt]),
      fractionValue_add a b ha hb, fractionValue_ofInt]
    norm_num
  change realHorner ((shifted (column (parentColumns p xl m) j)
    (Fraction.div (Fraction.add a b) (Fraction.ofInt 2)) Fraction.one).map fractionValue) _ = _
  rw [shifted_value _ _ _ _ hc hd (by decide), hv, fractionValue_one]
  congr 1
  ring

theorem ordinaryControl_saved_value (p : List (List Fraction)) (saved : List Fraction)
    (xl a b : Fraction) (m j : Nat) (v : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (hl : 0 < xl.den) (ha : 0 < a.den) (hb : 0 < b.den)
    (hcheck : Fraction.allEq (ordinaryControl p xl m j a b false false) saved = true) :
    realHorner ((column (parentColumns p xl m) j).map fractionValue) v =
      realHorner (saved.map fractionValue) (v-(fractionValue a+fractionValue b)/2) := by
  have h := ordinaryControl_centered_value p xl a b m j v hp hl ha hb
  rw [fraction_allEq_sound _ _ hcheck] at h
  exact h.symm

theorem ordinaryControl_norm_positive (p : List (List Fraction)) (saved : List Fraction)
    (xl a b radius : Fraction) (m j : Nat) (v : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hs : ∀ c ∈ saved, 0 < c.den)
    (hl : 0 < xl.den) (ha : 0 < a.den) (hb : 0 < b.den) (hr : 0 < radius.den)
    (hv : |v-(fractionValue a+fractionValue b)/2| ≤ fractionValue radius)
    (hreconstruct : Fraction.allEq (ordinaryControl p xl m j a b false false) saved = true)
    (hcheck : Fraction.positive (normMargin saved radius) = true) :
    0 < realHorner ((column (parentColumns p xl m) j).map fractionValue) v := by
  rw [ordinaryControl_saved_value p saved xl a b m j v hp hl ha hb hreconstruct]
  exact normMargin_sound saved radius _ hs hr hv hcheck

theorem ordinaryControl_quadratic_positive (p : List (List Fraction)) (saved : List Fraction)
    (xl a b radius : Fraction) (m j : Nat) (v : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hs : ∀ c ∈ saved, 0 < c.den)
    (hl : 0 < xl.den) (ha : 0 < a.den) (hb : 0 < b.den) (hr : 0 < radius.den)
    (hv : |v-(fractionValue a+fractionValue b)/2| ≤ fractionValue radius)
    (hreconstruct : Fraction.allEq (ordinaryControl p xl m j a b false false) saved = true)
    (hcheck : quadraticCheck saved radius = true) :
    0 < realHorner ((column (parentColumns p xl m) j).map fractionValue) v := by
  rw [ordinaryControl_saved_value p saved xl a b m j v hp hl ha hb hreconstruct]
  exact quadraticCheck_sound saved radius _ hs hr hv hcheck

theorem parent_bernstein_rectangle_positive (p : List (List Fraction)) (xl : Fraction)
    (m : Nat) (v x : ℝ) (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den)
    (hl : 0 < xl.den) (hm : ∀ row ∈ p, row.length ≤ m+1)
    (hl1 : fractionValue xl < 1) (hx0 : fractionValue xl ≤ x) (hx1 : x ≤ 1)
    (hcontrols : ∀ j ≤ m, 0 < realHorner ((column (parentColumns p xl m) j).map fractionValue) v) :
    0 < matrixValue p v x := by
  let t := (x-fractionValue xl)/(1-fractionValue xl)
  have hd : 0 < 1-fractionValue xl := sub_pos.mpr hl1
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hx0) hd.le
  have ht1 : t ≤ 1 := (div_le_one hd).mpr (by linarith only [hx1])
  have heq : fractionValue xl+(1-fractionValue xl)*t = x := by
    dsimp [t]
    field_simp
    <;> ring
  rw [← heq, parentColumns_value p xl m v t hp hl hm]
  simpa only [mul_comm] using bernstein_positive_combination m
    (fun j => realHorner ((column (parentColumns p xl m) j).map fractionValue) v)
    t ht0 ht1 hcontrols

end F4Heavy.Analysis
