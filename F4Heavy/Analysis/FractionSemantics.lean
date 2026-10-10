module

public import F4Heavy.Finite.Arithmetic
public import F4Heavy.Analysis.Quadratic
public import Mathlib.Data.Int.CharZero
public import Mathlib.Data.Nat.Cast.Field

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

noncomputable def fractionValue (a : Fraction) : ℝ := (a.num : ℝ) / (a.den : ℝ)

theorem fractionValue_ofInt (n : Int) : fractionValue (Fraction.ofInt n) = (n : ℝ) := by
  simp [fractionValue, Fraction.ofInt]

theorem fractionValue_zero : fractionValue Fraction.zero = 0 := by
  simp [Fraction.zero, fractionValue_ofInt]

theorem fractionValue_one : fractionValue Fraction.one = 1 := by
  simp [Fraction.one, fractionValue_ofInt]

theorem fractionValue_neg (a : Fraction) : fractionValue (Fraction.neg a) = -fractionValue a := by
  simp [fractionValue, Fraction.neg, neg_div]

theorem fractionValue_pow (a : Fraction) (n : Nat) :
    fractionValue (Fraction.pow a n) = fractionValue a ^ n := by
  simp [fractionValue, Fraction.pow, div_pow]

theorem fraction_eq_sound (a b : Fraction) (h : Fraction.eq a b = true) :
    fractionValue a = fractionValue b := by
  have hp : 0 < a.den ∧ 0 < b.den ∧ a.num * (b.den : Int) = b.num * (a.den : Int) := by
    simpa [Fraction.eq, and_assoc] using h
  have ha : (a.den : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp.1)
  have hb : (b.den : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hp.2.1)
  apply (div_eq_div_iff ha hb).2
  exact_mod_cast hp.2.2

theorem fraction_lt_sound (a b : Fraction) (h : Fraction.lt a b = true) :
    fractionValue a < fractionValue b := by
  have hp : 0 < a.den ∧ 0 < b.den ∧ a.num * (b.den : Int) < b.num * (a.den : Int) := by
    simpa [Fraction.lt, and_assoc] using h
  apply (div_lt_div_iff₀ (by exact_mod_cast hp.1 : (0 : ℝ) < a.den)
    (by exact_mod_cast hp.2.1 : (0 : ℝ) < b.den)).2
  exact_mod_cast hp.2.2

theorem fraction_le_sound (a b : Fraction) (h : Fraction.le a b = true) :
    fractionValue a ≤ fractionValue b := by
  have hp : 0 < a.den ∧ 0 < b.den ∧ a.num * (b.den : Int) ≤ b.num * (a.den : Int) := by
    simpa [Fraction.le, and_assoc] using h
  apply (div_le_div_iff₀ (by exact_mod_cast hp.1 : (0 : ℝ) < a.den)
    (by exact_mod_cast hp.2.1 : (0 : ℝ) < b.den)).2
  exact_mod_cast hp.2.2

theorem fraction_positive_sound (a : Fraction) (h : Fraction.positive a = true) :
    0 < fractionValue a := by
  have hp : 0 < a.den ∧ 0 < a.num := by simpa [Fraction.positive] using h
  exact div_pos (by exact_mod_cast hp.2) (by exact_mod_cast hp.1)

theorem fraction_eq_complete (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den)
    (h : fractionValue a = fractionValue b) : Fraction.eq a b = true := by
  have hcross := (div_eq_div_iff (ne_of_gt (by exact_mod_cast ha : (0 : ℝ) < a.den))
    (ne_of_gt (by exact_mod_cast hb : (0 : ℝ) < b.den))).mp h
  have hi : a.num * (b.den : Int) = b.num * (a.den : Int) := by exact_mod_cast hcross
  simp [Fraction.eq, ha, hb, hi]

theorem fraction_lt_complete (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den)
    (h : fractionValue a < fractionValue b) : Fraction.lt a b = true := by
  have hcross := (div_lt_div_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a.den)
    (by exact_mod_cast hb : (0 : ℝ) < b.den)).mp h
  have hi : a.num * (b.den : Int) < b.num * (a.den : Int) := by exact_mod_cast hcross
  simp [Fraction.lt, ha, hb, hi]

theorem fraction_le_complete (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den)
    (h : fractionValue a ≤ fractionValue b) : Fraction.le a b = true := by
  have hcross := (div_le_div_iff₀ (by exact_mod_cast ha : (0 : ℝ) < a.den)
    (by exact_mod_cast hb : (0 : ℝ) < b.den)).mp h
  have hi : a.num * (b.den : Int) ≤ b.num * (a.den : Int) := by exact_mod_cast hcross
  simp [Fraction.le, ha, hb, hi]

theorem fraction_normalize_den_pos (n : Int) (d : Nat) (hd : 0 < d) :
    0 < (Fraction.normalize n d).den := by
  exact Nat.div_pos (Nat.gcd_le_right n.natAbs hd) (Nat.gcd_pos_of_pos_right _ hd)

theorem fractionValue_normalize (n : Int) (d : Nat) (hd : 0 < d) :
    fractionValue (Fraction.normalize n d) = (n : ℝ) / (d : ℝ) := by
  have hgn : (n.natAbs.gcd d : Int) ∣ n := Int.natCast_dvd.mpr (Nat.gcd_dvd_left _ _)
  have hgd : n.natAbs.gcd d ∣ d := Nat.gcd_dvd_right _ _
  have hg : (n.natAbs.gcd d : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.gcd_pos_of_pos_right n.natAbs hd)
  simp only [fractionValue, Fraction.normalize]
  rw [Int.cast_div_charZero hgn, Nat.cast_div_charZero hgd, Int.cast_natCast]
  exact div_div_div_cancel_right₀ hg _ _

theorem fraction_mul_den_pos (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (Fraction.mul a b).den := by
  exact fraction_normalize_den_pos _ _ (Nat.mul_pos ha hb)

theorem fractionValue_mul (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    fractionValue (Fraction.mul a b) = fractionValue a * fractionValue b := by
  unfold Fraction.mul
  rw [fractionValue_normalize _ _ (Nat.mul_pos ha hb)]
  simp [fractionValue, div_mul_div_comm]

theorem fraction_add_den_pos (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (Fraction.add a b).den := by
  exact fraction_normalize_den_pos _ _ (Nat.mul_pos
    (Nat.div_pos (Nat.gcd_le_left b.den ha) (Nat.gcd_pos_of_pos_left _ ha)) hb)

theorem fractionValue_add (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    fractionValue (Fraction.add a b) = fractionValue a + fractionValue b := by
  have hg : (a.den.gcd b.den : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast Nat.gcd_pos_of_pos_left b.den ha)
  have haR : (a.den : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast ha)
  have hbR : (b.den : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hb)
  have had : 0 < a.den / a.den.gcd b.den :=
    Nat.div_pos (Nat.gcd_le_left b.den ha) (Nat.gcd_pos_of_pos_left _ ha)
  unfold Fraction.add
  rw [fractionValue_normalize _ _ (Nat.mul_pos had hb)]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast, Nat.cast_mul,
    Nat.cast_div_charZero (Nat.gcd_dvd_left a.den b.den),
    Nat.cast_div_charZero (Nat.gcd_dvd_right a.den b.den), fractionValue]
  field_simp
  <;> ring

theorem fraction_sub_den_pos (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    0 < (Fraction.sub a b).den := by
  exact fraction_add_den_pos a (Fraction.neg b) ha hb

theorem fractionValue_sub (a b : Fraction) (ha : 0 < a.den) (hb : 0 < b.den) :
    fractionValue (Fraction.sub a b) = fractionValue a - fractionValue b := by
  rw [Fraction.sub, fractionValue_add a (Fraction.neg b) ha hb, fractionValue_neg]
  rfl

theorem fraction_inv_den_pos (a : Fraction) (hn : a.num ≠ 0) :
    0 < (Fraction.inv a).den := by
  exact Int.natAbs_pos.mpr hn

theorem fractionValue_inv (a : Fraction) : fractionValue (Fraction.inv a) = (fractionValue a)⁻¹ := by
  unfold fractionValue Fraction.inv
  split_ifs with hn
  · have habs : (a.num.natAbs : ℝ) = -(a.num : ℝ) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using
        congrArg (fun z : Int => (z : ℝ)) (Int.ofNat_natAbs_of_nonpos hn.le)
    simp [habs, inv_div]
  · have habs : (a.num.natAbs : ℝ) = (a.num : ℝ) := by
      simpa only [Int.cast_natCast] using
        congrArg (fun z : Int => (z : ℝ)) (Int.natAbs_of_nonneg (le_of_not_gt hn))
    simp [habs, inv_div]

theorem fraction_div_den_pos (a b : Fraction) (ha : 0 < a.den) (hb : b.num ≠ 0) :
    0 < (Fraction.div a b).den := by
  exact fraction_mul_den_pos _ _ ha (fraction_inv_den_pos b hb)

theorem fractionValue_div (a b : Fraction) (ha : 0 < a.den) (hb : b.num ≠ 0) :
    fractionValue (Fraction.div a b) = fractionValue a / fractionValue b := by
  rw [Fraction.div, fractionValue_mul _ _ ha (fraction_inv_den_pos b hb), fractionValue_inv]
  rfl

theorem fractionValue_abs (a : Fraction) : fractionValue (Fraction.abs a) = |fractionValue a| := by
  simp [fractionValue, Fraction.abs, abs_div]

theorem fraction_foldl_add_den_pos (xs : List Fraction) (acc : Fraction) (ha : 0 < acc.den)
    (hx : ∀ x ∈ xs, 0 < x.den) : 0 < (xs.foldl Fraction.add acc).den := by
  induction xs generalizing acc with
  | nil => exact ha
  | cons x xs ih =>
    exact ih (Fraction.add acc x) (fraction_add_den_pos acc x ha (hx x (by simp)))
      (fun y hy => hx y (by simp [hy]))

theorem fractionValue_foldl_add (xs : List Fraction) (acc : Fraction) (ha : 0 < acc.den)
    (hx : ∀ x ∈ xs, 0 < x.den) :
    fractionValue (xs.foldl Fraction.add acc) = fractionValue acc + (xs.map fractionValue).sum := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (Fraction.add acc x) (fraction_add_den_pos acc x ha (hx x (by simp)))
      (fun y hy => hx y (by simp [hy])), fractionValue_add acc x ha (hx x (by simp))]
    ring

theorem fraction_sum_den_pos (xs : List Fraction) (hx : ∀ x ∈ xs, 0 < x.den) :
    0 < (Fraction.sum xs).den := by
  exact fraction_foldl_add_den_pos xs Fraction.zero (by decide) hx

theorem fractionValue_sum (xs : List Fraction) (hx : ∀ x ∈ xs, 0 < x.den) :
    fractionValue (Fraction.sum xs) = (xs.map fractionValue).sum := by
  rw [Fraction.sum, fractionValue_foldl_add xs Fraction.zero (by decide) hx, fractionValue_zero, zero_add]

end F4Heavy.Analysis
