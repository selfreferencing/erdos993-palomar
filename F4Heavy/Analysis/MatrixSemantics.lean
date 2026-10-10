module

public import F4Heavy.Analysis.BernsteinSemantics
public import F4Heavy.Analysis.ProjectiveSemantics

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Heavy.Finite

/-- Dense source matrices have activity rows and parent-variable columns. -/
noncomputable def matrixValue (p : List (List Fraction)) (v x : ℝ) : ℝ :=
  realHorner (p.map (fun row => realHorner (row.map fractionValue) x)) v

theorem realHorner_map_add {α : Type} (p : List α) (f g : α → ℝ) (x : ℝ) :
    realHorner (p.map (fun a => f a + g a)) x =
      realHorner (p.map f) x + realHorner (p.map g) x := by
  induction p with
  | nil => simp [realHorner]
  | cons a p ih => simp only [List.map_cons, realHorner_cons, ih]; ring

theorem realHorner_map_zero {α : Type} (p : List α) (x : ℝ) :
    realHorner (p.map (fun _ => (0 : ℝ))) x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [List.map_cons, realHorner_cons, ih, mul_zero, add_zero]

theorem realHorner_map_sum {α β : Type} (p : List α) (s : Finset β)
    (f : β → α → ℝ) (x : ℝ) :
    realHorner (p.map (fun a => ∑ j ∈ s, f j a)) x =
      ∑ j ∈ s, realHorner (p.map (f j)) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, realHorner_map_zero]
  | @insert b s hb ih =>
    simp only [Finset.sum_insert hb, realHorner_map_add, ih]

theorem matrixEq_value (p q : List (List Fraction)) (v x : ℝ)
    (h : matrixEq p q = true) : matrixValue p v x = matrixValue q v x := by
  have he := congrArg (fun a : List (List ℝ) =>
    realHorner (a.map (fun row => realHorner row x)) v) (matrixEq_sound p q h)
  simpa [matrixValue, List.map_map, Function.comp_def] using he

theorem parentColumns_den_pos (p : List (List Fraction)) (xl : Fraction) (m : Nat)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den) :
    ∀ row ∈ parentColumns p xl m, ∀ c ∈ row, 0 < c.den := by
  intro row hr
  change row ∈ p.map (fun r => bernstein r xl Fraction.one m) at hr
  obtain ⟨r, hrow, rfl⟩ := List.mem_map.mp hr
  exact bernstein_den_pos r xl Fraction.one m (hp r hrow) hl (by decide)

theorem column_den_pos (p : List (List Fraction)) (j : Nat)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) :
    ∀ c ∈ column p j, 0 < c.den := by
  intro c hc
  obtain ⟨row, hr, rfl⟩ := List.mem_map.mp hc
  exact fractionGet_den_pos row j (hp row hr)

/-- The original bivariate polynomial equals its parent Bernstein expansion. -/
theorem parentColumns_value (p : List (List Fraction)) (xl : Fraction)
    (m : Nat) (v t : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ m+1) :
    matrixValue p v (fractionValue xl + (1-fractionValue xl)*t) =
      ∑ j ∈ Finset.range (m+1), bernsteinWeight m j t *
        realHorner ((column (parentColumns p xl m) j).map fractionValue) v := by
  unfold matrixValue
  have hr : p.map (fun row => realHorner (row.map fractionValue)
      (fractionValue xl + (1-fractionValue xl)*t)) =
      p.map (fun row => ∑ j ∈ Finset.range (m+1),
        bernsteinWeight m j t * fractionValue ((bernstein row xl Fraction.one m)[j]?.getD Fraction.zero)) := by
    apply List.map_congr_left
    intro row hrow
    have h := bernstein_value row xl Fraction.one m t (hp row hrow) hl (by decide) (hm row hrow)
    simpa only [fractionValue_one, mul_comm] using h.symm
  rw [hr, realHorner_map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [column, parentColumns, List.map_map, Function.comp_def] using
    realHorner_map_scale (p.map (fun row =>
      fractionValue ((bernstein row xl Fraction.one m)[j]?.getD Fraction.zero)))
      (bernsteinWeight m j t) v

/-- Homogenization turns a parent Bernstein expansion into an ordinary polynomial. -/
theorem bernstein_projective_weight (m j : Nat) (t : ℝ) (hj : j ≤ m)
    (ht : 1-t ≠ 0) :
    bernsteinWeight m j t = (1-t)^m * (m.choose j : ℝ) * (t/(1-t))^j := by
  unfold bernsteinWeight
  rw [div_pow, pow_sub₀ (1-t) ht hj]
  ring

theorem parentColumns_projective_value (p : List (List Fraction)) (xl : Fraction)
    (m : Nat) (v t : ℝ)
    (hp : ∀ row ∈ p, ∀ c ∈ row, 0 < c.den) (hl : 0 < xl.den)
    (hm : ∀ row ∈ p, row.length ≤ m+1) (ht : 1-t ≠ 0) :
    matrixValue p v (fractionValue xl + (1-fractionValue xl)*t) =
      (1-t)^m * realHorner ((List.range (m+1)).map (fun j =>
        (m.choose j : ℝ) * realHorner
          ((column (parentColumns p xl m) j).map fractionValue) v)) (t/(1-t)) := by
  rw [parentColumns_value p xl m v t hp hl hm, realHorner_map_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [bernstein_projective_weight m j t (by have := Finset.mem_range.mp hj; omega) ht]
  ring

end F4Heavy.Analysis
