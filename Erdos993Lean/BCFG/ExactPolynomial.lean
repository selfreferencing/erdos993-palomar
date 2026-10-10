module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

/-!
Executable ascending coefficient lists over Lean's exact `Rat`, interpreted
in the reals by Horner evaluation.
No finite packet result is assumed here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

open scoped BigOperators

abbrev Uni := List Rat

namespace Uni

noncomputable def evalReal : Uni → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * evalReal p x

def add : Uni → Uni → Uni
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : Rat) : Uni → Uni
  | [] => []
  | b :: p => (a * b) :: scale a p

def mul : Uni → Uni → Uni
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def pow (p : Uni) : Nat → Uni
  | 0 => [1]
  | n + 1 => mul (pow p n) p

def comp : Uni → Uni → Uni
  | [], _ => []
  | a :: p, q => add [a] (mul q (comp p q))

def sum : List Uni → Uni
  | [] => []
  | p :: ps => add p (sum ps)

def sumRange (f : Nat → Uni) : Nat → Uni
  | 0 => []
  | n + 1 => add (sumRange f n) (f n)

def monomial (a : Rat) : Nat → Uni
  | 0 => [a]
  | n + 1 => 0 :: monomial a n

/-- Remove trailing zero coefficients only. -/
def trim : Uni → Uni
  | [] => []
  | a :: p =>
      let t := trim p
      if a = 0 ∧ t = [] then [] else a :: t

@[simp] theorem evalReal_nil (x : ℝ) : evalReal [] x = 0 := rfl

@[simp] theorem evalReal_cons (a : Rat) (p : Uni) (x : ℝ) :
    evalReal (a :: p) x = (a : ℝ) + x * evalReal p x := rfl

@[simp] theorem evalReal_singleton (a : Rat) (x : ℝ) :
    evalReal [a] x = (a : ℝ) := by
  simp [evalReal]

@[simp] theorem evalReal_add (p q : Uni) (x : ℝ) :
    evalReal (add p q) x = evalReal p x + evalReal q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
      cases q with
      | nil => simp [add]
      | cons b q =>
          simp only [add, evalReal_cons, Rat.cast_add, ih]
          ring

@[simp] theorem evalReal_scale (a : Rat) (p : Uni) (x : ℝ) :
    evalReal (scale a p) x = (a : ℝ) * evalReal p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
      simp only [scale, evalReal_cons, Rat.cast_mul, ih]
      ring

@[simp] theorem evalReal_mul (p q : Uni) (x : ℝ) :
    evalReal (mul p q) x = evalReal p x * evalReal q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
      simp only [mul, evalReal_add, evalReal_scale, evalReal_cons, Rat.cast_zero, ih]
      ring

@[simp] theorem evalReal_pow (p : Uni) (n : Nat) (x : ℝ) :
    evalReal (pow p n) x = evalReal p x ^ n := by
  induction n with
  | zero => simp [pow]
  | succ n ih => simp [pow, evalReal_mul, ih, pow_succ]

@[simp] theorem evalReal_comp (p q : Uni) (x : ℝ) :
    evalReal (comp p q) x = evalReal p (evalReal q x) := by
  induction p with
  | nil => simp [comp]
  | cons a p ih =>
      simp only [comp, evalReal_add, evalReal_singleton, evalReal_mul,
        ih, evalReal_cons, evalReal_nil, mul_zero, add_zero]

@[simp] theorem evalReal_sum (ps : List Uni) (x : ℝ) :
    evalReal (sum ps) x = (ps.map (fun p => evalReal p x)).sum := by
  induction ps with
  | nil => simp [sum]
  | cons p ps ih => simp [sum, ih]

@[simp] theorem evalReal_sumRange (f : Nat → Uni) (n : Nat) (x : ℝ) :
    evalReal (sumRange f n) x = ∑ j ∈ Finset.range n, evalReal (f j) x := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, Finset.sum_range_succ]

@[simp] theorem evalReal_monomial (a : Rat) (n : Nat) (x : ℝ) :
    evalReal (monomial a n) x = (a : ℝ) * x ^ n := by
  induction n with
  | zero => simp [monomial]
  | succ n ih =>
      simp only [monomial, evalReal_cons, Rat.cast_zero, zero_add, ih, pow_succ]
      ring

@[simp] theorem evalReal_trim (p : Uni) (x : ℝ) :
    evalReal (trim p) x = evalReal p x := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      simp only [trim]
      split_ifs with h
      · rcases h with ⟨ha, ht⟩
        have hp : evalReal p x = 0 := by
          rw [← ih, ht]
          rfl
        simp [evalReal, ha, hp]
      · simp only [evalReal_cons, ih]

/-- Semantic equality after optional canonicalization is sufficient; the
algorithm does not rely on any claim that `trim` produces a unique normal form. -/
theorem evalReal_eq_of_trim_eq {p q : Uni} (h : trim p = trim q) (x : ℝ) :
    evalReal p x = evalReal q x := by
  rw [← evalReal_trim p x, h, evalReal_trim]

def checkEq (p q : Uni) : Bool := decide (trim p = trim q)

theorem checkEq_sound {p q : Uni} (h : checkEq p q = true) (x : ℝ) :
    evalReal p x = evalReal q x := by
  exact evalReal_eq_of_trim_eq (of_decide_eq_true h) x

/-- Coefficients of one Bernstein basis polynomial, with no restriction on j.
The positivity consumer separately restricts j to `0,...,M`. -/
def bernBasis (M j : Nat) : Uni :=
  scale (M.choose j : Rat) (mul (monomial 1 j) (pow [1, -1] (M - j)))

@[simp] theorem evalReal_one_sub (x : ℝ) :
    evalReal [1, -1] x = 1 - x := by
  simp [evalReal, sub_eq_add_neg]

theorem evalReal_bernBasis (M j : Nat) (x : ℝ) :
    evalReal (bernBasis M j) x =
      (M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j) := by
  simp [bernBasis, mul_assoc, sub_eq_add_neg]

def bernPoly (M : Nat) (c : Nat → Rat) : Uni :=
  sumRange (fun j => scale (c j) (bernBasis M j)) (M + 1)

theorem evalReal_bernPoly (M : Nat) (c : Nat → Rat) (x : ℝ) :
    evalReal (bernPoly M c) x =
      ∑ j ∈ Finset.range (M + 1),
        (c j : ℝ) * ((M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j)) := by
  simp only [bernPoly, evalReal_sumRange, evalReal_scale, evalReal_bernBasis]

/-- An explicit degree is retained: absent list entries are zero, so a short
vector cannot pass a strict positivity check for every index through M. -/
def bernVector (M : Nat) (c : List Rat) : Uni :=
  bernPoly M (fun j => c.getD j 0)

theorem evalReal_bernVector (M : Nat) (c : List Rat) (x : ℝ) :
    evalReal (bernVector M c) x =
      ∑ j ∈ Finset.range (M + 1),
        (c.getD j 0 : ℝ) * ((M.choose j : ℝ) * x ^ j * (1 - x) ^ (M - j)) := by
  exact evalReal_bernPoly M (fun j => c.getD j 0) x

/-- This is the exact identity used to restrict a polynomial to [a,b]. -/
theorem evalReal_affine_comp (p : Uni) (a b : Rat) (x : ℝ) :
    evalReal (comp p [a, b - a]) x =
      evalReal p ((a : ℝ) + ((b : ℝ) - (a : ℝ)) * x) := by
  rw [evalReal_comp]
  congr 1
  simp [evalReal, mul_comm]

end Uni

end Erdos993Lean.BCFG
