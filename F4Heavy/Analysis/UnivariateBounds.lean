module

public import F4Heavy.Analysis.FractionSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

noncomputable def realHorner (p : List ℝ) (x : ℝ) : ℝ :=
  p.foldr (fun a z => a + x * z) 0

theorem realHorner_nil (x : ℝ) : realHorner [] x = 0 := rfl

theorem realHorner_cons (a : ℝ) (p : List ℝ) (x : ℝ) :
    realHorner (a :: p) x = a + x * realHorner p x := rfl

theorem evalPoly_den_pos (p : List Fraction) (x : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hx : 0 < x.den) : 0 < (evalPoly p x).den := by
  induction p with
  | nil => exact Nat.zero_lt_one
  | cons a p ih =>
    exact fraction_add_den_pos a (Fraction.mul x (evalPoly p x)) (hp a (by simp))
      (fraction_mul_den_pos _ _ hx (ih (fun b hb => hp b (by simp [hb]))))

theorem evalPoly_value (p : List Fraction) (x : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hx : 0 < x.den) :
    fractionValue (evalPoly p x) = realHorner (p.map fractionValue) (fractionValue x) := by
  induction p with
  | nil => exact fractionValue_zero
  | cons a p ih =>
    have hpp : ∀ b ∈ p, 0 < b.den := fun b hb => hp b (by simp [hb])
    have hden := evalPoly_den_pos p x hpp hx
    change fractionValue (Fraction.add a (Fraction.mul x (evalPoly p x))) = _
    rw [fractionValue_add _ _ (hp a (by simp)) (fraction_mul_den_pos _ _ hx hden),
      fractionValue_mul _ _ hx hden, ih hpp]
    rfl

theorem realHorner_nonneg (p : List ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hp : ∀ a ∈ p, 0 ≤ a) : 0 ≤ realHorner p x := by
  induction p with
  | nil => exact le_refl 0
  | cons a p ih =>
    exact add_nonneg (hp a (by simp)) (mul_nonneg hx (ih (fun b hb => hp b (by simp [hb]))))

theorem realHorner_constant_lower (a : ℝ) (p : List ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hp : ∀ b ∈ p, 0 ≤ b) : a ≤ realHorner (a :: p) x := by
  exact le_add_of_nonneg_right (mul_nonneg hx (realHorner_nonneg p x hx hp))

theorem realHorner_positive (a : ℝ) (p : List ℝ) (x : ℝ) (ha : 0 < a) (hx : 0 ≤ x)
    (hp : ∀ b ∈ p, 0 ≤ b) : 0 < realHorner (a :: p) x :=
  lt_of_lt_of_le ha (realHorner_constant_lower a p x hx hp)

theorem realHorner_abs_bound (p : List ℝ) (x r : ℝ) (hxr : |x| ≤ r) :
    |realHorner p x| ≤ realHorner (p.map abs) r := by
  have hr : 0 ≤ r := (abs_nonneg x).trans hxr
  induction p with
  | nil => simp [realHorner]
  | cons a p ih =>
    simp only [List.map_cons, realHorner_cons]
    calc
      |a + x * realHorner p x| ≤ |a| + |x * realHorner p x| := abs_add_le _ _
      _ = |a| + |x| * |realHorner p x| := by rw [abs_mul]
      _ ≤ |a| + r * realHorner (p.map abs) r :=
        add_le_add_right (mul_le_mul hxr ih (abs_nonneg _) hr) _

theorem realHorner_centered_lower (a : ℝ) (p : List ℝ) (x r : ℝ) (hxr : |x| ≤ r) :
    a - r * realHorner (p.map abs) r ≤ realHorner (a :: p) x := by
  have hr : 0 ≤ r := (abs_nonneg x).trans hxr
  have hh := realHorner_abs_bound p x r hxr
  have hm := mul_le_mul hxr hh (abs_nonneg (realHorner p x)) hr
  rw [← abs_mul] at hm
  have hlow := (abs_le.mp hm).1
  rw [realHorner_cons]
  linarith

theorem zipIdx_power_sum (p : List Fraction) (f : Fraction → ℝ) (x : ℝ) (start : Nat) :
    ((p.zipIdx start).map fun ak => f ak.1 * x ^ ak.2).sum =
      x ^ start * realHorner (p.map f) x := by
  induction p generalizing start with
  | nil => simp [realHorner]
  | cons a p ih =>
    simp only [List.zipIdx_cons, List.map_cons, List.sum_cons, realHorner_cons]
    rw [ih (start + 1), pow_succ]
    ring

theorem zipIdx_shifted_power_sum (p : List Fraction) (f : Fraction → ℝ) (x : ℝ) (start : Nat) :
    ((p.zipIdx start).map fun ak => f ak.1 * x ^ (ak.2 - start)).sum =
      realHorner (p.map f) x := by
  rw [List.zipIdx_eq_map_add]
  simp only [List.map_map, Function.comp_def, Nat.add_sub_cancel_left]
  simpa only [pow_zero, one_mul] using zipIdx_power_sum p f x 0

theorem tailNorm_den_pos (p : List Fraction) (r : Fraction) (start : Nat)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) : 0 < (tailNorm p r start).den := by
  apply fraction_sum_den_pos
  intro b hb
  obtain ⟨ak, hak, rfl⟩ := List.mem_map.mp hb
  have ha := hp ak.1 (List.mem_of_mem_drop (List.fst_mem_of_mem_zipIdx hak))
  exact fraction_mul_den_pos _ _ ha (pow_pos hr _)

theorem tailNorm_value (p : List Fraction) (r : Fraction) (start : Nat)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) :
    fractionValue (tailNorm p r start) =
      realHorner ((p.drop start).map fun a => |fractionValue a|) (fractionValue r) := by
  have hden : ∀ b ∈ ((p.drop start).zipIdx start).map
      (fun ak => Fraction.mul (Fraction.abs ak.1) (Fraction.pow r (ak.2 - start))), 0 < b.den := by
    intro b hb
    obtain ⟨ak, hak, rfl⟩ := List.mem_map.mp hb
    exact fraction_mul_den_pos _ _
      (hp ak.1 (List.mem_of_mem_drop (List.fst_mem_of_mem_zipIdx hak))) (pow_pos hr _)
  rw [tailNorm, fractionValue_sum _ hden]
  rw [List.map_map]
  have heq : (((p.drop start).zipIdx start).map fun ak =>
      fractionValue (Fraction.mul (Fraction.abs ak.1) (Fraction.pow r (ak.2 - start)))) =
      (((p.drop start).zipIdx start).map fun ak =>
        |fractionValue ak.1| * fractionValue r ^ (ak.2 - start)) := by
    apply List.map_congr_left
    intro ak hak
    rw [fractionValue_mul (Fraction.abs ak.1) (Fraction.pow r (ak.2 - start))
      (hp ak.1 (List.mem_of_mem_drop (List.fst_mem_of_mem_zipIdx hak))) (pow_pos hr _),
      fractionValue_abs, fractionValue_pow]
  change (List.map (fun ak => fractionValue (Fraction.mul (Fraction.abs ak.1)
    (Fraction.pow r (ak.2 - start)))) ((p.drop start).zipIdx start)).sum = _
  rw [heq]
  exact zipIdx_shifted_power_sum (p.drop start) (fun a => |fractionValue a|) (fractionValue r) start

theorem fractionHead_den_pos (p : List Fraction) (hp : ∀ a ∈ p, 0 < a.den) :
    0 < (p[0]?.getD Fraction.zero).den := by
  cases p with
  | nil => exact Nat.zero_lt_one
  | cons a p => exact hp a (by simp)

theorem normMargin_value (p : List Fraction) (r : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) :
    fractionValue (normMargin p r) =
      (199 / 200 : ℝ) * fractionValue (p[0]?.getD Fraction.zero) -
        fractionValue r * realHorner ((p.drop 1).map fun a => |fractionValue a|) (fractionValue r) := by
  have hh := fractionHead_den_pos p hp
  have ht := tailNorm_den_pos p r 1 hp hr
  unfold normMargin
  rw [fractionValue_sub (Fraction.mul ⟨199, 200⟩ (p[0]?.getD Fraction.zero))
    (Fraction.mul r (tailNorm p r 1))
    (fraction_mul_den_pos _ _ (by decide) hh) (fraction_mul_den_pos _ _ hr ht),
    fractionValue_mul ⟨199, 200⟩ _ (by decide) hh, fractionValue_mul r _ hr ht,
    tailNorm_value p r 1 hp hr]
  have hc : fractionValue ⟨199, 200⟩ = (199 / 200 : ℝ) := by norm_num [fractionValue]
  rw [hc]

theorem lowerColumn_value (p : List Fraction) (r : Fraction)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) :
    fractionValue (lowerColumn p r) = fractionValue (p[0]?.getD Fraction.zero) -
      fractionValue r * realHorner ((p.drop 1).map fun a => |fractionValue a|) (fractionValue r) := by
  have hh := fractionHead_den_pos p hp
  have ht := tailNorm_den_pos p r 1 hp hr
  unfold lowerColumn
  rw [fractionValue_sub _ (Fraction.mul r (tailNorm p r 1)) hh (fraction_mul_den_pos _ _ hr ht),
    fractionValue_mul r _ hr ht, tailNorm_value p r 1 hp hr]

theorem lowerColumn_sound (p : List Fraction) (r : Fraction) (x : ℝ)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) (hxr : |x| ≤ fractionValue r) :
    fractionValue (lowerColumn p r) ≤ realHorner (p.map fractionValue) x := by
  rw [lowerColumn_value p r hp hr]
  cases p with
  | nil => simp [fractionValue_zero, realHorner]
  | cons a p =>
    simpa only [List.getElem?_cons_zero, Option.getD_some, List.drop_succ_cons, List.drop_zero,
      List.map_cons, List.map_map, Function.comp_def] using
      realHorner_centered_lower (fractionValue a) (p.map fractionValue) x (fractionValue r) hxr

theorem normMargin_sound (p : List Fraction) (r : Fraction) (x : ℝ)
    (hp : ∀ a ∈ p, 0 < a.den) (hr : 0 < r.den) (hxr : |x| ≤ fractionValue r)
    (hcheck : Fraction.positive (normMargin p r) = true) :
    0 < realHorner (p.map fractionValue) x := by
  have hm := fraction_positive_sound (normMargin p r) hcheck
  rw [normMargin_value p r hp hr] at hm
  have hrv : 0 ≤ fractionValue r := (abs_nonneg x).trans hxr
  have ht : 0 ≤ realHorner ((p.drop 1).map fun a => |fractionValue a|) (fractionValue r) := by
    apply realHorner_nonneg _ _ hrv
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact abs_nonneg _
  have hrt := mul_nonneg hrv ht
  have hh : 0 < fractionValue (p[0]?.getD Fraction.zero) := by linarith
  have hl := lowerColumn_sound p r x hp hr hxr
  rw [lowerColumn_value p r hp hr] at hl
  linarith

end F4Heavy.Analysis
