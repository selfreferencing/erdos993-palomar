module

public import F4Heavy.Finite.TransformArithmetic
public import F4Heavy.Analysis.UnivariateBounds
public import Mathlib.Data.Nat.Choose.Basic

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

theorem choose_fold_value (n k : Nat) :
    (List.range k).foldl (fun acc i => acc * (n - i) / (i + 1)) 1 = n.choose k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih,
      ← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

theorem choose_value (n k : Nat) : F4Heavy.Finite.choose n k = n.choose k := by
  unfold F4Heavy.Finite.choose
  split
  · rename_i h
    exact (Nat.choose_eq_zero_of_lt h).symm
  · exact choose_fold_value n k

theorem choose_den_positive (n k : Nat) (hk : k ≤ n) : 0 < F4Heavy.Finite.choose n k := by
  rw [choose_value]
  exact Nat.choose_pos hk

theorem fraction_allEq_sound (p q : List Fraction) (h : Fraction.allEq p q = true) :
    p.map fractionValue = q.map fractionValue := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => simp [Fraction.allEq] at h
  | cons a p ih =>
    cases q with
    | nil => simp [Fraction.allEq] at h
    | cons b q =>
      have hh : p.length = q.length ∧ Fraction.eq a b = true ∧
          (p.zip q).all (fun ab => Fraction.eq ab.1 ab.2) = true := by
        simpa [Fraction.allEq, and_assoc] using h
      have ht : Fraction.allEq p q = true := by simp [Fraction.allEq, hh.1, hh.2.2]
      simp only [List.map_cons, fraction_eq_sound a b hh.2.1, ih q ht]

theorem matrixEq_sound (p q : List (List Fraction)) (h : matrixEq p q = true) :
    p.map (List.map fractionValue) = q.map (List.map fractionValue) := by
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons b q => simp [matrixEq] at h
  | cons a p ih =>
    cases q with
    | nil => simp [matrixEq] at h
    | cons b q =>
      have hh : p.length = q.length ∧ Fraction.allEq a b = true ∧
          (p.zip q).all (fun ab => Fraction.allEq ab.1 ab.2) = true := by
        simpa [matrixEq, and_assoc] using h
      have ht : matrixEq p q = true := by simp [matrixEq, hh.1, hh.2.2]
      simp only [List.map_cons, fraction_allEq_sound a b hh.2.1, ih q ht]

theorem realHorner_map_scale (p : List ℝ) (c x : ℝ) :
    realHorner (p.map (fun a => c * a)) x = c * realHorner p x := by
  induction p with
  | nil => simp [realHorner]
  | cons a p ih => simp only [List.map_cons, realHorner_cons, ih]; ring

theorem realHorner_map_mono {α : Type} (p : List α) (f g : α → ℝ) (x : ℝ)
    (hx : 0 ≤ x) (hfg : ∀ a ∈ p, f a ≤ g a) :
    realHorner (p.map f) x ≤ realHorner (p.map g) x := by
  induction p with
  | nil => exact le_refl _
  | cons a p ih =>
    exact add_le_add (hfg a (by simp))
      (mul_le_mul_of_nonneg_left (ih (fun b hb => hfg b (by simp [hb]))) hx)

theorem primitiveLowerCheck_value (cols : List (List Fraction)) (r scale : Fraction)
    (p : List Fraction) (x : ℝ) (hp : ∀ a ∈ p, 0 < a.den)
    (hcheck : primitiveLowerCheck cols r scale p = true) :
    fractionValue scale * realHorner (p.map fractionValue) x =
      realHorner (cols.map (fun c => fractionValue (lowerColumn c r))) x := by
  have hh : Fraction.positive scale = true ∧
      Fraction.allEq (p.map (Fraction.mul scale)) (cols.map (fun c => lowerColumn c r)) = true := by
    simpa only [primitiveLowerCheck, Bool.and_eq_true] using hcheck
  have hs : 0 < scale.den := by
    have h : 0 < scale.den ∧ 0 < scale.num := by simpa [Fraction.positive] using hh.1
    exact h.1
  have heq := fraction_allEq_sound _ _ hh.2
  simp only [List.map_map, Function.comp_def] at heq
  have hmap : p.map (fun a => fractionValue (Fraction.mul scale a)) =
      (p.map fractionValue).map (fun a => fractionValue scale * a) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro a ha
    exact fractionValue_mul scale a hs (hp a ha)
  rw [hmap] at heq
  rw [← realHorner_map_scale, heq]

theorem primitiveLowerCheck_sound (cols : List (List Fraction)) (r scale : Fraction)
    (p : List Fraction) (v x : ℝ) (hp : ∀ a ∈ p, 0 < a.den)
    (hcols : ∀ c ∈ cols, ∀ a ∈ c, 0 < a.den) (hr : 0 < r.den)
    (hv : |v| ≤ fractionValue r) (hx : 0 ≤ x)
    (hcheck : primitiveLowerCheck cols r scale p = true) :
    fractionValue scale * realHorner (p.map fractionValue) x ≤
      realHorner (cols.map (fun c => realHorner (c.map fractionValue) v)) x := by
  rw [primitiveLowerCheck_value cols r scale p x hp hcheck]
  exact realHorner_map_mono cols _ _ x hx
    (fun c hc => lowerColumn_sound c r v (hcols c hc) hr hv)

theorem primitiveLowerCheck_positive (cols : List (List Fraction)) (r scale : Fraction)
    (p : List Fraction) (v x : ℝ) (hp : ∀ a ∈ p, 0 < a.den)
    (hcols : ∀ c ∈ cols, ∀ a ∈ c, 0 < a.den) (hr : 0 < r.den)
    (hv : |v| ≤ fractionValue r) (hx : 0 ≤ x)
    (hcheck : primitiveLowerCheck cols r scale p = true)
    (hpos : 0 < realHorner (p.map fractionValue) x) :
    0 < realHorner (cols.map (fun c => realHorner (c.map fractionValue) v)) x := by
  have hs : Fraction.positive scale = true := (Bool.and_eq_true_iff.mp hcheck).1
  exact lt_of_lt_of_le (mul_pos (fraction_positive_sound scale hs) hpos)
    (primitiveLowerCheck_sound cols r scale p v x hp hcols hr hv hx hcheck)

end F4Heavy.Analysis
