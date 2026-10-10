module

public import Erdos993Lean.F4Fast.IntegerPolynomial
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.F4Fast.RangeAll

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.F4Fast.P04Int

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

/-- The finite arithmetic behind equation (44), with a common denominator.
Every operation in this definition is over integers or natural indices. -/
def weightedCoefficient (n m : Nat) (Z : List (List Int))
    (K : Nat → Nat → Int) (A B : Nat) : Int :=
  ((List.range (A+1)).map fun i =>
    ((List.range (B+1)).map fun j =>
      (Z.getD i []).getD j 0 * (A.choose i : Int) * (B.choose j : Int) * K i j).sum).sum

theorem sum_fraction_cast {α : Type} (xs : List α) (f : α → Int) (D : Rat) :
    (xs.map (fun a => (f a : Rat) / D)).sum = ((xs.map f).sum : Rat) / D := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Int.cast_add, add_div]

/-- Integer cross-products for the binomial weights recover the unchanged
rational coefficient formula. The domain guards are explicit bounded premises;
no particular coefficient or denominator is assumed. -/
theorem bernCoefficient_eq_integer (n m : Nat) (p : Bi) (Z : List (List Int))
    (D W : Int) (K : Nat → Nat → Int) (hD : D ≠ 0) (hW : W ≠ 0)
    (hp : ∀ i < n+1, ∀ j < m+1,
      (p.getD i []).getD j 0 = ((Z.getD i []).getD j 0 : Rat) / (D : Rat))
    (hK : ∀ i < n+1, ∀ j < m+1,
      K i j * (n.choose i : Int) * (m.choose j : Int) = W)
    (A B : Nat) (hA : A ≤ n) (hB : B ≤ m) :
    bernCoefficient n m p A B =
      (weightedCoefficient n m Z K A B : Rat) / ((D : Rat) * (W : Rat)) := by
  have hd : (D : Rat) ≠ 0 := by exact_mod_cast hD
  have hw : (W : Rat) ≠ 0 := by exact_mod_cast hW
  unfold bernCoefficient weightedCoefficient
  calc
    _ = ((List.range (A+1)).map fun i =>
        (((List.range (B+1)).map fun j =>
          (Z.getD i []).getD j 0 * (A.choose i : Int) * (B.choose j : Int) * K i j).sum : Rat) /
            ((D : Rat) * (W : Rat))).sum := by
      congr 1
      apply List.map_congr_left
      intro i hi
      have hin : i < n+1 := lt_of_lt_of_le (List.mem_range.mp hi) (Nat.add_le_add_right hA 1)
      rw [← sum_fraction_cast]
      congr 1
      apply List.map_congr_left
      intro j hj
      have hjm : j < m+1 := lt_of_lt_of_le (List.mem_range.mp hj) (Nat.add_le_add_right hB 1)
      rw [hp i hin j hjm]
      have hk : (K i j : Rat) * (n.choose i : Rat) * (m.choose j : Rat) = (W : Rat) := by
        exact_mod_cast hK i hin j hjm
      have hn : (n.choose i : Rat) ≠ 0 := by
        intro hz
        simp only [hz, mul_zero, zero_mul] at hk
        exact hw hk.symm
      have hm : (m.choose j : Rat) ≠ 0 := by
        intro hz
        simp only [hz, mul_zero] at hk
        exact hw hk.symm
      simp only [Int.cast_mul, Int.cast_natCast]
      apply (div_eq_div_iff (mul_ne_zero hn hm) (mul_ne_zero hd hw)).2
      rw [← hk]
      field_simp [hd]
      <;> ring
    _ = _ := sum_fraction_cast _ _ _

/-- A cleared comparison over a positive denominator implies the current
Rat lower comparison. This is a field/order theorem, not numerical evaluation. -/
theorem lower_of_integer (c z D : Int) (hD : 0 < D)
    (h : c * D ≤ 100 * z) :
    (c : Rat) ≤ 100 * ((z : Rat) / (D : Rat)) := by
  have hd : (0 : Rat) < D := by exact_mod_cast hD
  have hc : (c : Rat) * (D : Rat) ≤ 100 * (z : Rat) := by exact_mod_cast h
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hd).2 hc

/-- Recover a whole original Boolean row from a pure integer row fact. -/
theorem lower_row_of_integer (m A : Nat) (b : Nat → Nat → Rat)
    (c : List Rat) (C : List Int) (z : Nat → Int) (D : Int)
    (hD : 0 < D) (hc : c.getD A 0 = (C.getD A 0 : Rat))
    (hb : ∀ B < m+1, b A B = (z B : Rat) / (D : Rat))
    (hcheck : (decide (0 < C.getD A 0) &&
      (List.range (m+1)).all (fun B => decide (C.getD A 0 * D ≤ 100*z B))) = true) :
    (decide (0 < c.getD A 0) &&
      (List.range (m+1)).all (fun B => decide (c.getD A 0 ≤ 100*b A B))) = true := by
  rcases Bool.and_eq_true_iff.mp hcheck with ⟨hpos, hrow⟩
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true_eq.mpr
    rw [hc]
    exact_mod_cast (of_decide_eq_true hpos : 0 < C.getD A 0)
  · apply List.all_eq_true.mpr
    intro B hB
    have hlt := List.mem_range.mp hB
    have hnum : C.getD A 0 * D ≤ 100*z B :=
      of_decide_eq_true (List.all_eq_true.mp hrow B hB)
    apply decide_eq_true_eq.mpr
    rw [hc, hb B hlt]
    exact lower_of_integer _ _ _ hD hnum

end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.F4Fast.P04Int.bernCoefficient_eq_integer
#print axioms Erdos993Lean.F4Fast.P04Int.lower_of_integer
#print axioms Erdos993Lean.F4Fast.P04Int.lower_row_of_integer
