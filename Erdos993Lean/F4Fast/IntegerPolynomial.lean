module

public import Erdos993Lean.F4Fast.CachedNormalization
public import Lean.Elab.Tactic.Omega

/-!
Generic integer polynomials. Every operation has the exact
list recursion of the original rational operation, retaining all trailing
zeros. The cast identities and guarded homogeneous affine composition are
proved over arbitrary integer inputs; no finite certificate data is used.

-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

abbrev IUni := List Int

namespace IUni

def add : IUni → IUni → IUni
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: add p q

def scale (a : Int) : IUni → IUni
  | [] => []
  | b :: p => (a*b) :: scale a p

def mul : IUni → IUni → IUni
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

def pow (p : IUni) : Nat → IUni
  | 0 => [1]
  | n+1 => mul (pow p n) p

def sumRange (f : Nat → IUni) : Nat → IUni
  | 0 => []
  | n+1 => add (sumRange f n) (f n)

def monomial (a : Int) : Nat → IUni
  | 0 => [a]
  | n+1 => 0 :: monomial a n

def bernBasis (M j : Nat) : IUni :=
  scale (M.choose j : Int) (mul (monomial 1 j) (pow [1,-1] (M-j)))

def castRat (p : IUni) : Uni := p.map (fun z : Int => (z : Rat))

theorem castRat_add (p q : IUni) :
    castRat (add p q) = Uni.add (castRat p) (castRat q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      simp only [add, castRat, List.map_cons, Uni.add, Int.cast_add]
      exact congrArg (List.cons ((a : Rat)+(b : Rat))) (ih q)

theorem castRat_scale (a : Int) (p : IUni) :
    castRat (scale a p) = Uni.scale (a : Rat) (castRat p) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [scale, castRat, List.map_cons, Uni.scale, Int.cast_mul]
    exact congrArg (List.cons ((a : Rat)*(b : Rat))) ih

theorem castRat_mul (p q : IUni) :
    castRat (mul p q) = Uni.mul (castRat p) (castRat q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [mul, castRat_add, castRat_scale]
    simp only [castRat, List.map_cons, Int.cast_zero, Uni.mul]
    exact congrArg (Uni.add (Uni.scale (a : Rat) (castRat q)))
      (congrArg (List.cons 0) ih)

theorem castRat_pow (p : IUni) (n : Nat) :
    castRat (pow p n) = Uni.pow (castRat p) n := by
  induction n with
  | zero => simp [pow, castRat, Uni.pow]
  | succ n ih =>
    rw [pow, castRat_mul, ih, Uni.pow]

theorem castRat_sumRange (f : Nat → IUni) (n : Nat) :
    castRat (sumRange f n) = Uni.sumRange (fun j => castRat (f j)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange, castRat_add, ih, Uni.sumRange]

theorem castRat_getD (p : IUni) (i : Nat) :
    (castRat p).getD i 0 = (p.getD i 0 : Rat) := by
  induction p generalizing i with
  | nil => simp [castRat]
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [castRat, List.map_cons, List.getD_cons_succ] using ih i

theorem castRat_monomial (a : Int) (n : Nat) :
    castRat (monomial a n) = Uni.monomial (a : Rat) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [monomial, castRat, List.map_cons, Int.cast_zero, Uni.monomial]
    exact congrArg (List.cons 0) ih

theorem castRat_bernBasis (M j : Nat) :
    castRat (bernBasis M j) = Uni.bernBasis M j := by
  rw [bernBasis, castRat_scale, castRat_mul, castRat_monomial, castRat_pow]
  simp only [Uni.bernBasis, Int.cast_natCast, Int.cast_one, castRat,
    List.map_cons, List.map_nil, Int.cast_neg]

theorem rat_scale_add (s : Rat) (p q : Uni) :
    Uni.scale s (Uni.add p q) = Uni.add (Uni.scale s p) (Uni.scale s q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q => simp only [Uni.add, Uni.scale, mul_add, ih]

theorem rat_scale_scale (s t : Rat) (p : Uni) :
    Uni.scale s (Uni.scale t p) = Uni.scale (s*t) p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [Uni.scale, ih, mul_assoc]

theorem rat_scale_sumRange (s : Rat) (f : Nat → Uni) (n : Nat) :
    Uni.scale s (Uni.sumRange f n) =
      Uni.sumRange (fun j => Uni.scale s (f j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Uni.sumRange, rat_scale_add, ih]

theorem rat_mul_scale_left (s : Rat) (p q : Uni) :
    Uni.mul (Uni.scale s p) q = Uni.scale s (Uni.mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [Uni.scale, Uni.mul, rat_scale_add, rat_scale_scale, ih, mul_zero]

theorem rat_mul_scale_right (s : Rat) (p q : Uni) :
    Uni.mul p (Uni.scale s q) = Uni.scale s (Uni.mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [Uni.scale, Uni.mul, rat_scale_add, rat_scale_scale, ih, mul_zero,
      mul_comm]

theorem rat_mul_scaled (s t : Rat) (p q : Uni) :
    Uni.mul (Uni.scale s p) (Uni.scale t q) =
      Uni.scale (s*t) (Uni.mul p q) := by
  rw [rat_mul_scale_left, rat_mul_scale_right, rat_scale_scale]

theorem rat_pow_scale (s : Rat) (p : Uni) (n : Nat) :
    Uni.pow (Uni.scale s p) n = Uni.scale (s^n) (Uni.pow p n) := by
  induction n with
  | zero => simp [Uni.pow, Uni.scale]
  | succ n ih =>
    rw [Uni.pow, ih, rat_mul_scaled, pow_succ, Uni.pow]

theorem rat_pow_scaled (p : IUni) (s : Rat) (n : Nat) :
    Uni.pow (Uni.scale s (castRat p)) n =
      Uni.scale (s^n) (castRat (pow p n)) := by
  rw [rat_pow_scale, castRat_pow]

def affineHom (p : IUni) (A B D : Int) (M : Nat) : IUni :=
  match p with
  | [] => []
  | a :: tail =>
    add [a*D^M] (mul [A,B] (affineHom tail A B D (M-1)))

theorem affineHom_cast (p : IUni) (A B D : Int) (M : Nat)
    (hlen : p.length ≤ M+1) (hD : (D : Rat) ≠ 0) :
    Uni.comp (castRat p) [(A : Rat)/(D : Rat),(B : Rat)/(D : Rat)] =
      Uni.scale (((D : Rat)^M)⁻¹) (castRat (affineHom p A B D M)) := by
  induction p generalizing M with
  | nil => rfl
  | cons a p ih =>
    cases M with
    | zero =>
      cases p with
      | nil =>
        simp [affineHom, castRat, add, mul, scale, Uni.comp, Uni.add,
          Uni.mul, Uni.scale]
      | cons b p =>
        simp only [List.length_cons] at hlen
        omega
    | succ M =>
      have hlen' : p.length ≤ M+1 := by
        simp only [List.length_cons] at hlen
        omega
      have hrec := ih M hlen'
      have hcast :
          castRat (affineHom (a :: p) A B D (M+1)) =
            Uni.add [(a : Rat)*(D : Rat)^(M+1)]
              (Uni.mul [(A : Rat),(B : Rat)]
                (castRat (affineHom p A B D M))) := by
        rw [affineHom, castRat_add, castRat_mul]
        simp only [Nat.add_sub_cancel, castRat, List.map_cons, List.map_nil,
          Int.cast_mul, Int.cast_pow]
      have hhead :
          ((D : Rat)^(M+1))⁻¹ * ((a : Rat)*(D : Rat)^(M+1)) = (a : Rat) := by
        rw [mul_left_comm, inv_mul_cancel₀ (pow_ne_zero _ hD), mul_one]
      have hq : [(A : Rat)/(D : Rat),(B : Rat)/(D : Rat)] =
          Uni.scale ((D : Rat)⁻¹) [(A : Rat),(B : Rat)] := by
        simp only [Uni.scale, div_eq_mul_inv, mul_comm]
      change Uni.add [(a : Rat)]
          (Uni.mul [(A : Rat)/(D : Rat),(B : Rat)/(D : Rat)]
            (Uni.comp (castRat p) [(A : Rat)/(D : Rat),(B : Rat)/(D : Rat)])) = _
      rw [hrec, hcast, rat_scale_add]
      congr 1
      · simp only [Uni.scale]
        rw [hhead]
      · rw [hq, rat_mul_scaled, pow_succ, mul_inv_rev]

end IUni

end Erdos993Lean.BCFG

#print axioms Erdos993Lean.BCFG.IUni.castRat_add
#print axioms Erdos993Lean.BCFG.IUni.castRat_scale
#print axioms Erdos993Lean.BCFG.IUni.castRat_mul
#print axioms Erdos993Lean.BCFG.IUni.castRat_pow
#print axioms Erdos993Lean.BCFG.IUni.castRat_sumRange
#print axioms Erdos993Lean.BCFG.IUni.castRat_getD
#print axioms Erdos993Lean.BCFG.IUni.castRat_bernBasis
#print axioms Erdos993Lean.BCFG.IUni.rat_mul_scaled
#print axioms Erdos993Lean.BCFG.IUni.rat_pow_scaled
#print axioms Erdos993Lean.BCFG.IUni.affineHom_cast
