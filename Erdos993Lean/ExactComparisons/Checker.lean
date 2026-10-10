module

public import Std
public import Init.Data.Rat.Lemmas

/-!
Exact rational comparisons using integer cross-products. The executable
checker does not normalize rationals. Soundness interprets every record in
Lean's core `Rat` type; nonpositive denominators are rejected explicitly.
This module is independent of Mathlib.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Erdos993Lean.ExactComparisons

open scoped Rat

inductive Relation where
  | lt
  | le
  | eq
  deriving DecidableEq, Repr

structure Comparison where
  leftNum : Int
  leftDen : Int
  rightNum : Int
  rightDen : Int
  relation : Relation := .lt
  deriving Repr, DecidableEq

def Comparison.crossHolds (c : Comparison) : Prop :=
  match c.relation with
  | .lt => c.leftNum * c.rightDen < c.rightNum * c.leftDen
  | .le => c.leftNum * c.rightDen ≤ c.rightNum * c.leftDen
  | .eq => c.leftNum * c.rightDen = c.rightNum * c.leftDen

instance (c : Comparison) : Decidable c.crossHolds := by
  unfold Comparison.crossHolds
  cases c.relation <;> infer_instance

def Comparison.check (c : Comparison) : Bool :=
  decide (0 < c.leftDen ∧ 0 < c.rightDen ∧ c.crossHolds)

def Comparison.rationalHolds (c : Comparison) : Prop :=
  0 < c.leftDen ∧ 0 < c.rightDen ∧
    match c.relation with
    | .lt => (c.leftNum /. c.leftDen) < (c.rightNum /. c.rightDen)
    | .le => (c.leftNum /. c.leftDen) ≤ (c.rightNum /. c.rightDen)
    | .eq => (c.leftNum /. c.leftDen) = (c.rightNum /. c.rightDen)

theorem divInt_le_iff_cross (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    (a /. b) ≤ (c /. d) ↔ a * d ≤ c * b := by
  rw [Rat.le_iff_sub_nonneg,
    Rat.divInt_sub_divInt c a (Int.ne_of_gt hd) (Int.ne_of_gt hb),
    Rat.divInt_nonneg_iff_of_pos_right (Int.mul_pos hd hb)]
  omega

theorem divInt_lt_iff_cross (a b c d : Int) (hb : 0 < b) (hd : 0 < d) :
    (a /. b) < (c /. d) ↔ a * d < c * b := by
  rw [← Rat.not_le, divInt_le_iff_cross c d a b hd hb, Int.not_le]

theorem Comparison.check_sound (c : Comparison) (h : c.check = true) :
    c.rationalHolds := by
  have h' : 0 < c.leftDen ∧ 0 < c.rightDen ∧ c.crossHolds :=
    of_decide_eq_true h
  refine ⟨h'.1, h'.2.1, ?_⟩
  cases hr : c.relation with
  | lt =>
    exact (divInt_lt_iff_cross _ _ _ _ h'.1 h'.2.1).mpr
      (by simpa [Comparison.crossHolds, hr] using h'.2.2)
  | le =>
    exact (divInt_le_iff_cross _ _ _ _ h'.1 h'.2.1).mpr
      (by simpa [Comparison.crossHolds, hr] using h'.2.2)
  | eq =>
    exact (Rat.divInt_eq_divInt_iff (Int.ne_of_gt h'.1) (Int.ne_of_gt h'.2.1)).mpr
      (by simpa [Comparison.crossHolds, hr] using h'.2.2)

def check (records : List Comparison) : Bool := records.all Comparison.check

theorem check_sound (records : List Comparison) (h : check records = true) :
    ∀ c ∈ records, c.rationalHolds := by
  intro c hc
  apply Comparison.check_sound
  exact (List.all_eq_true.mp h) c hc

/-- Retain a source expression in a sample while exposing its integer data. -/
def Comparison.ofRats (a b : Rat) (r : Relation := .lt) : Comparison :=
  ⟨a.num, a.den, b.num, b.den, r⟩

theorem rat_num_den (a : Rat) : a.num /. (a.den : Int) = a := by
  cases a
  exact Rat.mk_eq_divInt.symm

theorem Comparison.ofRats_sound (a b : Rat) (r : Relation)
    (h : (Comparison.ofRats a b r).check = true) :
    match r with
    | .lt => a < b
    | .le => a ≤ b
    | .eq => a = b := by
  have h' := (Comparison.check_sound _ h).2.2
  cases r <;> simpa [Comparison.rationalHolds, Comparison.ofRats, rat_num_den] using h'

/- Edge cases are kernel checks: signs, unreduced inputs, weak comparison,
equality, and invalid denominators. -/
example : check [⟨-3, 7, -2, 5, .lt⟩, ⟨2, 4, 1, 2, .eq⟩,
    ⟨-8, 6, 0, 1, .le⟩, ⟨5, 11, 10, 22, .le⟩] = true := by decide
example : check [⟨1, 0, 2, 3, .lt⟩] = false := by decide
example : check [⟨1, -2, 0, 1, .lt⟩] = false := by decide
example : check [⟨1, 2, 1, 2, .lt⟩] = false := by decide

#print axioms Comparison.check_sound
#print axioms check_sound

end Erdos993Lean.ExactComparisons
