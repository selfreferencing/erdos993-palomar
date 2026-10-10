module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi

/-! Integer product check for rational coefficient lists (nothing existing is changed by this file).

Integer mirror of the project's coefficient-list operations, with ONE common denominator per
list, and a generic soundness theorem: a product of two rational coefficient lists can be
checked by one integer multiplication plus three linear passes, instead of a quadratic number
of gcd-normalised `Rat` operations inside the kernel.  No numerical fact is asserted here. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace

abbrev IUni := List Int
abbrev IBi := List IUni

namespace IUni

def add : IUni → IUni → IUni
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : Int) : IUni → IUni
  | [] => []
  | b :: p => (a * b) :: scale a p

def mul : IUni → IUni → IUni
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

/-- The rational list with the common denominator `D` restored. -/
def cast (D : ℕ) (p : IUni) : Uni := p.map (fun z => (z : ℚ) / (D : ℚ))

theorem cast_cons (D : ℕ) (a : Int) (p : IUni) :
    cast D (a :: p) = ((a : ℚ) / (D : ℚ)) :: cast D p := rfl

theorem cast_add (D : ℕ) (p q : IUni) : Uni.add (cast D p) (cast D q) = cast D (add p q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      show ((a : ℚ) / (D : ℚ) + (b : ℚ) / (D : ℚ)) :: Uni.add (cast D p) (cast D q) =
        (((a + b : ℤ) : ℚ) / (D : ℚ)) :: cast D (add p q)
      rw [ih, Int.cast_add, add_div]

theorem cast_scale (D E : ℕ) (a : Int) (q : IUni) :
    Uni.scale ((a : ℚ) / (D : ℚ)) (cast E q) = cast (D * E) (scale a q) := by
  induction q with
  | nil => rfl
  | cons b q ih =>
    show ((a : ℚ) / (D : ℚ) * ((b : ℚ) / (E : ℚ))) :: Uni.scale ((a : ℚ) / (D : ℚ)) (cast E q) =
      (((a * b : ℤ) : ℚ) / ((D * E : ℕ) : ℚ)) :: cast (D * E) (scale a q)
    rw [ih, Int.cast_mul, Nat.cast_mul, div_mul_div_comm]

theorem cast_mul (D E : ℕ) (p q : IUni) :
    Uni.mul (cast D p) (cast E q) = cast (D * E) (mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    show Uni.add (Uni.scale ((a : ℚ) / (D : ℚ)) (cast E q))
        (0 :: Uni.mul (cast D p) (cast E q)) =
      cast (D * E) (add (scale a q) (0 :: mul p q))
    rw [cast_scale, ih, ← cast_add, cast_cons, Int.cast_zero, zero_div]

end IUni

namespace IBi

def add : IBi → IBi → IBi
  | [], q => q
  | p, [] => p
  | p :: ps, q :: qs => IUni.add p q :: add ps qs

def innerMul (a : IUni) (p : IBi) : IBi := p.map (IUni.mul a)

def mul : IBi → IBi → IBi
  | [], _ => []
  | a :: p, q => add (innerMul a q) ([] :: mul p q)

def cast (D : ℕ) (P : IBi) : Bi := P.map (IUni.cast D)

theorem cast_add (D : ℕ) (P Q : IBi) : Bi.add (cast D P) (cast D Q) = cast D (add P Q) := by
  induction P generalizing Q with
  | nil => rfl
  | cons p P ih =>
    cases Q with
    | nil => rfl
    | cons q Q =>
      show Uni.add (IUni.cast D p) (IUni.cast D q) :: Bi.add (cast D P) (cast D Q) =
        IUni.cast D (IUni.add p q) :: cast D (add P Q)
      rw [ih, IUni.cast_add]

theorem cast_innerMul (D E : ℕ) (a : IUni) (Q : IBi) :
    FinitePolynomial.innerMul (IUni.cast D a) (cast E Q) = cast (D * E) (innerMul a Q) := by
  induction Q with
  | nil => rfl
  | cons q Q ih =>
    show Uni.mul (IUni.cast D a) (IUni.cast E q) ::
        FinitePolynomial.innerMul (IUni.cast D a) (cast E Q) =
      IUni.cast (D * E) (IUni.mul a q) :: cast (D * E) (innerMul a Q)
    rw [ih, IUni.cast_mul]

theorem cast_mul (D E : ℕ) (P Q : IBi) :
    FinitePolynomial.mul (cast D P) (cast E Q) = cast (D * E) (mul P Q) := by
  induction P with
  | nil => rfl
  | cons a P ih =>
    show Bi.add (FinitePolynomial.innerMul (IUni.cast D a) (cast E Q))
        ([] :: FinitePolynomial.mul (cast D P) (cast E Q)) =
      cast (D * E) (add (innerMul a Q) ([] :: mul P Q))
    rw [cast_innerMul, ih, ← cast_add]
    rfl

end IBi

/-- Least common denominator of the entries of a rational coefficient list. -/
def denUni (p : Uni) (d : ℕ) : ℕ := p.foldl (fun d x => Nat.lcm d x.den) d
def denBi (P : Bi) : ℕ := P.foldl (fun d row => denUni row d) 1

/-- Numerators over the common denominator `D`. -/
def numsUni (D : ℕ) (p : Uni) : IUni := p.map (fun x => (x * (D : ℚ)).num)
def numsBi (D : ℕ) (P : Bi) : IBi := P.map (numsUni D)

def mulCheckNums (p a b : Bi) (D E : ℕ) (A B : IBi) : Bool :=
  decide (a = IBi.cast D A) && (decide (b = IBi.cast E B) &&
    decide (p = IBi.cast (D * E) (IBi.mul A B)))

def mulCheckDen (p a b : Bi) (D E : ℕ) : Bool :=
  mulCheckNums p a b D E (numsBi D a) (numsBi E b)

/-- One Boolean: `p` is the product of `a` and `b`, checked with integer arithmetic. -/
def mulCheck (p a b : Bi) : Bool := mulCheckDen p a b (denBi a) (denBi b)

theorem mul_of_nums {p a b : Bi} {D E : ℕ} {A B : IBi} (ha : a = IBi.cast D A)
    (hb : b = IBi.cast E B) (hp : p = IBi.cast (D * E) (IBi.mul A B)) :
    p = FinitePolynomial.mul a b := by
  subst ha hb hp
  exact (IBi.cast_mul D E A B).symm

/-- Generic soundness of the integer product check. -/
theorem mul_of_mulCheck {p a b : Bi} (h : mulCheck p a b = true) :
    p = FinitePolynomial.mul a b := by
  unfold mulCheck mulCheckDen mulCheckNums at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact mul_of_nums h.1 h.2.1 h.2.2

end Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly

#print axioms Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck
