module

public import Erdos993Lean.F4Fast.P04IntegerOrder
public import Mathlib.Algebra.Ring.Rat

/-! Exact raw-fraction source custody. These list maps expose literal Int/Nat
pairs without reducing Rat arithmetic in any finite check. Their generic
bridges retain arbitrary list shapes and getD zero/default semantics.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.F4Fast.P04Int

abbrev FractionPair := Int × Nat

def fraction (p : FractionPair) : Rat := (p.1 : Rat)/(p.2 : Rat)
def ratioList (p : List FractionPair) : List Rat := p.map fraction
def mkRatList (p : List FractionPair) : List Rat := p.map (fun x => mkRat x.1 x.2)
def ratioMatrix (p : List (List FractionPair)) : List (List Rat) := p.map ratioList
def mkRatMatrix (p : List (List FractionPair)) : List (List Rat) := p.map mkRatList

theorem mkRatList_eq_ratioList (p : List FractionPair) : mkRatList p = ratioList p := by
  unfold mkRatList ratioList
  apply List.map_congr_left
  intro x hx
  exact Rat.mkRat_eq_div x.1 x.2

theorem mkRatMatrix_eq_ratioMatrix (p : List (List FractionPair)) :
    mkRatMatrix p = ratioMatrix p := by
  unfold mkRatMatrix ratioMatrix
  apply List.map_congr_left
  intro x hx
  exact mkRatList_eq_ratioList x

theorem ratioList_getD (p : List FractionPair) (i : Nat) :
    (ratioList p).getD i 0 = fraction (p.getD i (0,1)) := by
  induction p generalizing i with
  | nil => simp [ratioList, fraction]
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [ratioList, List.map_cons, List.getD_cons_succ] using ih i

theorem ratioMatrix_getD (p : List (List FractionPair)) (i : Nat) :
    (ratioMatrix p).getD i [] = ratioList (p.getD i []) := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [ratioMatrix, List.map_cons, List.getD_cons_succ] using ih i

theorem ratioMatrix_getD_getD (p : List (List FractionPair)) (i j : Nat) :
    ((ratioMatrix p).getD i []).getD j 0 = fraction ((p.getD i []).getD j (0,1)) := by
  rw [ratioMatrix_getD, ratioList_getD]

theorem fractionPair_le (p q : FractionPair) (hp : 0 < p.2) (hq : 0 < q.2)
    (hcross : p.1*(q.2 : Int) ≤ q.1*(p.2 : Int)) : fraction p ≤ fraction q := by
  have hpI : (0 : Int) < (p.2 : Int) := by exact_mod_cast hp
  have hqI : (0 : Int) < (q.2 : Int) := by exact_mod_cast hq
  simpa only [fraction, Int.cast_natCast] using
    fraction_le p.1 (p.2 : Int) q.1 (q.2 : Int) hpI hqI hcross

theorem fractionPair_eq (p q : FractionPair) (hp : p.2 ≠ 0) (hq : q.2 ≠ 0)
    (hcross : p.1*(q.2 : Int) = q.1*(p.2 : Int)) : fraction p = fraction q := by
  have hpI : (p.2 : Int) ≠ 0 := by exact_mod_cast hp
  have hqI : (q.2 : Int) ≠ 0 := by exact_mod_cast hq
  simpa only [fraction, Int.cast_natCast] using
    fraction_eq p.1 (p.2 : Int) q.1 (q.2 : Int) hpI hqI hcross

end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.F4Fast.P04Int.mkRatList_eq_ratioList
#print axioms Erdos993Lean.F4Fast.P04Int.mkRatMatrix_eq_ratioMatrix
#print axioms Erdos993Lean.F4Fast.P04Int.ratioList_getD
#print axioms Erdos993Lean.F4Fast.P04Int.ratioMatrix_getD
#print axioms Erdos993Lean.F4Fast.P04Int.ratioMatrix_getD_getD
#print axioms Erdos993Lean.F4Fast.P04Int.fractionPair_le
#print axioms Erdos993Lean.F4Fast.P04Int.fractionPair_eq
