module

public import Erdos993Lean.F4Fast.IntegerPolynomial
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi
public import Mathlib.Algebra.Ring.Rat

/-! Exact integer coefficient-list arithmetic for the unchanged predicates.
No coefficient lists are identified only through evaluation. All casts commute
with the original list operations, including their zero padding and trim.
WholeBi keeps one explicit positive integer denominator and performs no gcd.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

def rscale (s : Rat) (p : Bi) : Bi := p.map (Uni.scale s)

theorem uni_scale_getD (s : Rat) (p : Uni) (i : Nat) :
    (Uni.scale s p).getD i 0 = s * p.getD i 0 := by
  induction p generalizing i with
  | nil => simp [Uni.scale]
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [Uni.scale, List.getD_cons_succ] using ih i

theorem rscale_getD (s : Rat) (p : Bi) (i : Nat) :
    (rscale s p).getD i [] = Uni.scale s (p.getD i []) := by
  induction p generalizing i with
  | nil => simp [rscale, Uni.scale]
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [rscale, List.map_cons, List.getD_cons_succ] using ih i

theorem rscale_getD_getD (s : Rat) (p : Bi) (i j : Nat) :
    ((rscale s p).getD i []).getD j 0 = s * (p.getD i []).getD j 0 := by
  rw [rscale_getD, uni_scale_getD]

theorem rscale_add (s : Rat) (p q : Bi) :
    rscale s (Bi.add p q) = Bi.add (rscale s p) (rscale s q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      simp only [Bi.add, rscale, List.map_cons, IUni.rat_scale_add] at ih ⊢
      rw [ih]

theorem rscale_scale (s t : Rat) (p : Bi) :
    rscale s (rscale t p) = rscale (s*t) p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [rscale, List.map_cons, IUni.rat_scale_scale] at ih ⊢
    rw [ih]

theorem uni_scale_one (p : Uni) : Uni.scale 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih => simp only [Uni.scale, one_mul, ih]

theorem rscale_one (p : Bi) : rscale 1 p = p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [rscale, List.map_cons, uni_scale_one] at ih ⊢
    rw [ih]

theorem rscale_sumRange (s : Rat) (f : Nat → Bi) (n : Nat) :
    rscale s (Bi.sumRange f n) = Bi.sumRange (fun j => rscale s (f j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Bi.sumRange, rscale_add, ih]

end Erdos993Lean.F4Fast.P04Int

namespace Erdos993Lean.BCFG
abbrev IBi := List IUni
namespace IBi

def add : IBi → IBi → IBi
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => IUni.add a b :: add p q

def scale (a : Int) (p : IBi) : IBi := p.map (IUni.scale a)
def innerMul (a : IUni) (p : IBi) : IBi := p.map (IUni.mul a)
def mul : IBi → IBi → IBi
  | [], _ => []
  | a :: p, q => add (innerMul a q) ([] :: mul p q)
def neg (p : IBi) : IBi := scale (-1) p
def pow (p : IBi) : Nat → IBi
  | 0 => [[1]]
  | n+1 => mul (pow p n) p
def tensor (u v : IUni) : IBi := u.map (fun c => IUni.scale c v)
def sumRange (f : Nat → IBi) : Nat → IBi
  | 0 => []
  | n+1 => add (sumRange f n) (f n)
def castRat (p : IBi) : Bi := p.map IUni.castRat

def trimRow : IUni → IUni
  | [] => []
  | a :: p =>
    let t := trimRow p
    if a = 0 ∧ t = [] then [] else a :: t

def trim : IBi → IBi
  | [] => []
  | p :: ps =>
    let p' := trimRow p
    let t := trim ps
    if p' = [] ∧ t = [] then [] else p' :: t

def checkEq (p q : IBi) : Bool := decide (trim p = trim q)

open Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

theorem castRat_add (p q : IBi) :
    castRat (add p q) = Bi.add (castRat p) (castRat q) := by
  induction p generalizing q with
  | nil => rfl
  | cons a p ih =>
    cases q with
    | nil => rfl
    | cons b q =>
      simp only [add, castRat, List.map_cons, Bi.add, IUni.castRat_add] at ih ⊢
      rw [ih]

theorem castRat_scale (a : Int) (p : IBi) :
    castRat (scale a p) = rscale (a : Rat) (castRat p) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [scale, castRat, List.map_cons, rscale, IUni.castRat_scale] at ih ⊢
    rw [ih]

theorem castRat_innerMul (a : IUni) (p : IBi) :
    castRat (innerMul a p) =
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul
        (IUni.castRat a) (castRat p) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [innerMul, castRat, List.map_cons,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul,
      IUni.castRat_mul] at ih ⊢
    rw [ih]

theorem castRat_mul (p q : IBi) :
    castRat (mul p q) =
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul
        (castRat p) (castRat q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    rw [mul, castRat_add, castRat_innerMul]
    simp only [castRat, List.map_cons, IUni.castRat, List.map_nil,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul] at ih ⊢
    rw [ih]

theorem castRat_neg (p : IBi) :
    castRat (neg p) =
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg (castRat p) := by
  simpa only [neg, Int.cast_neg, Int.cast_one, rscale,
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg] using castRat_scale (-1) p

theorem castRat_pow (p : IBi) (n : Nat) :
    castRat (pow p n) =
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow (castRat p) n := by
  induction n with
  | zero => simp [pow, castRat, IUni.castRat,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow]
  | succ n ih => rw [pow, castRat_mul, ih,
      Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow]

theorem castRat_tensor (u v : IUni) :
    castRat (tensor u v) = Bi.tensor (IUni.castRat u) (IUni.castRat v) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    change IUni.castRat (IUni.scale a v) :: castRat (tensor u v) =
      Uni.scale (a : Rat) (IUni.castRat v) :: Bi.tensor (IUni.castRat u) (IUni.castRat v)
    rw [IUni.castRat_scale, ih]

theorem castRat_sumRange (f : Nat → IBi) (n : Nat) :
    castRat (sumRange f n) = Bi.sumRange (fun j => castRat (f j)) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sumRange, castRat_add, ih, Bi.sumRange]

theorem castRat_getD (p : IBi) (i : Nat) :
    (castRat p).getD i [] = IUni.castRat (p.getD i []) := by
  induction p generalizing i with
  | nil => rfl
  | cons a p ih =>
    cases i with
    | zero => rfl
    | succ i => simpa only [castRat, List.map_cons, List.getD_cons_succ] using ih i

theorem castRat_getD_getD (p : IBi) (i j : Nat) :
    ((castRat p).getD i []).getD j 0 = ((p.getD i []).getD j 0 : Rat) := by
  rw [castRat_getD, IUni.castRat_getD]

theorem castRat_trimRow (p : IUni) :
    IUni.castRat (trimRow p) = Uni.trim (IUni.castRat p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change IUni.castRat (if a = 0 ∧ trimRow p = [] then [] else a :: trimRow p) =
      (if (a : Rat) = 0 ∧ Uni.trim (IUni.castRat p) = [] then []
        else (a : Rat) :: Uni.trim (IUni.castRat p))
    rw [← ih]
    have hzero : ((a : Rat) = 0) ↔ a = 0 := Int.cast_eq_zero
    have hnil : IUni.castRat (trimRow p) = [] ↔ trimRow p = [] := by simp [IUni.castRat]
    simp only [hzero, hnil]
    split_ifs <;> rfl

theorem castRat_trim (p : IBi) : castRat (trim p) = Bi.trim (castRat p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change castRat (if trimRow a = [] ∧ trim p = [] then []
      else trimRow a :: trim p) =
      (if Uni.trim (IUni.castRat a) = [] ∧ Bi.trim (castRat p) = [] then []
        else Uni.trim (IUni.castRat a) :: Bi.trim (castRat p))
    rw [← castRat_trimRow, ← ih]
    have hrow : IUni.castRat (trimRow a) = [] ↔ trimRow a = [] := by simp [IUni.castRat]
    have hnil : castRat (trim p) = [] ↔ trim p = [] := by simp [castRat]
    simp only [hrow, hnil]
    split_ifs <;> rfl

end IBi
end Erdos993Lean.BCFG

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

theorem innerMul_scaled (s t : Rat) (a : Uni) (p : Bi) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul (Uni.scale s a) (rscale t p) = rscale (s*t) (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul a p) := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    simp only [Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul, rscale,
      List.map_cons, IUni.rat_mul_scaled] at ih ⊢
    rw [ih]

theorem mul_scaled (s t : Rat) (p q : Bi) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul (rscale s p) (rscale t q) = rscale (s*t) (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change Bi.add (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.innerMul
      (Uni.scale s a) (rscale t q))
      ([] :: Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul (rscale s p) (rscale t q)) = _
    rw [innerMul_scaled, ih, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul, rscale_add]
    rfl

theorem pow_scaled (s : Rat) (p : Bi) (n : Nat) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow (rscale s p) n = rscale (s^n) (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow p n) := by
  induction n with
  | zero => simp [Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow, rscale, Uni.scale]
  | succ n ih => rw [Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow, ih, mul_scaled, pow_succ, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow]

theorem neg_scaled (s : Rat) (p : Bi) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg (rscale s p) = rscale s (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg p) := by
  change rscale (-1) (rscale s p) = rscale s (rscale (-1) p)
  rw [rscale_scale, rscale_scale, mul_comm]

theorem tensor_scaled (s t : Rat) (u v : Uni) :
    Bi.tensor (Uni.scale s u) (Uni.scale t v) = rscale (s*t) (Bi.tensor u v) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    change Uni.scale (s*a) (Uni.scale t v) ::
      Bi.tensor (Uni.scale s u) (Uni.scale t v) =
      Uni.scale (s*t) (Uni.scale a v) :: rscale (s*t) (Bi.tensor u v)
    rw [ih, IUni.rat_scale_scale, IUni.rat_scale_scale]
    congr 2
    ring

theorem uni_trim_scale (s : Rat) (hs : s ≠ 0) (p : Uni) :
    Uni.trim (Uni.scale s p) = Uni.scale s (Uni.trim p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (if s*a = 0 ∧ Uni.trim (Uni.scale s p) = [] then []
      else (s*a) :: Uni.trim (Uni.scale s p)) =
      Uni.scale s (if a = 0 ∧ Uni.trim p = [] then [] else a :: Uni.trim p)
    rw [ih]
    have hz : s*a = 0 ↔ a = 0 := by simp [hs]
    have hn : Uni.scale s (Uni.trim p) = [] ↔ Uni.trim p = [] := by
      cases Uni.trim p <;> simp [Uni.scale]
    simp only [hz, hn]
    split_ifs <;> rfl

theorem trim_rscale (s : Rat) (hs : s ≠ 0) (p : Bi) :
    Bi.trim (rscale s p) = rscale s (Bi.trim p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (if Uni.trim (Uni.scale s a) = [] ∧ Bi.trim (rscale s p) = []
      then [] else Uni.trim (Uni.scale s a) :: Bi.trim (rscale s p)) =
      rscale s (if Uni.trim a = [] ∧ Bi.trim p = [] then [] else Uni.trim a :: Bi.trim p)
    rw [uni_trim_scale _ hs, ih]
    have hr : Uni.scale s (Uni.trim a) = [] ↔ Uni.trim a = [] := by
      cases Uni.trim a <;> simp [Uni.scale]
    have hp : rscale s (Bi.trim p) = [] ↔ Bi.trim p = [] := by simp [rscale]
    simp only [hr, hp]
    split_ifs <;> rfl

end Erdos993Lean.F4Fast.P04Int

namespace Erdos993Lean.BCFG.IBi
open Erdos993Lean.F4Fast.P04Int

theorem checkEq_castRat (p q : IBi) (h : checkEq p q = true) :
    Bi.checkEq (castRat p) (castRat q) = true := by
  have ht : trim p = trim q := of_decide_eq_true h
  have hc := congrArg castRat ht
  rw [castRat_trim, castRat_trim] at hc
  simp [Bi.checkEq, hc]

theorem checkEq_of_scaled (D1 D2 : Int) (hD1 : D1 ≠ 0) (hD2 : D2 ≠ 0)
    (p q : IBi) (h : checkEq (scale D2 p) (scale D1 q) = true) :
    Bi.checkEq (rscale (1/(D1 : Rat)) (castRat p))
      (rscale (1/(D2 : Rat)) (castRat q)) = true := by
  have hd1 : (D1 : Rat) ≠ 0 := by exact_mod_cast hD1
  have hd2 : (D2 : Rat) ≠ 0 := by exact_mod_cast hD2
  have ht : trim (scale D2 p) = trim (scale D1 q) := of_decide_eq_true h
  have hr := congrArg castRat ht
  rw [castRat_trim, castRat_trim, castRat_scale, castRat_scale,
    trim_rscale _ hd2, trim_rscale _ hd1] at hr
  let s : Rat := 1/((D1 : Rat)*(D2 : Rat))
  have he := congrArg (rscale s) hr
  rw [rscale_scale, rscale_scale] at he
  have h1 : s*(D2 : Rat) = 1/(D1 : Rat) := by dsimp [s]; field_simp [hd1, hd2]
  have h2 : s*(D1 : Rat) = 1/(D2 : Rat) := by dsimp [s]; field_simp [hd1, hd2]
  rw [h1, h2] at he
  unfold Bi.checkEq
  rw [trim_rscale _ (div_ne_zero one_ne_zero hd1),
    trim_rscale _ (div_ne_zero one_ne_zero hd2), he]
  simp

end Erdos993Lean.BCFG.IBi

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

structure WholeBi where
  num : IBi
  den : Int
  deriving Repr

namespace WholeBi

def valid (p : WholeBi) : Prop := 0 < p.den
def recover (p : WholeBi) : Bi := rscale (1/(p.den : Rat)) (IBi.castRat p.num)
def constant (a : Rat) : WholeBi := ⟨[[a.num]], (a.den : Int)⟩
def add (p q : WholeBi) : WholeBi :=
  ⟨IBi.add (IBi.scale q.den p.num) (IBi.scale p.den q.num), p.den*q.den⟩
def neg (p : WholeBi) : WholeBi := ⟨IBi.neg p.num, p.den⟩
def mul (p q : WholeBi) : WholeBi := ⟨IBi.mul p.num q.num, p.den*q.den⟩
def pow (p : WholeBi) (n : Nat) : WholeBi := ⟨IBi.pow p.num n, p.den^n⟩

theorem valid_constant (a : Rat) : valid (constant a) := by
  change (0 : Int) < (a.den : Int)
  exact_mod_cast a.den_pos

theorem valid_add (p q : WholeBi) (hp : valid p) (hq : valid q) : valid (add p q) :=
  Int.mul_pos hp hq

theorem valid_neg (p : WholeBi) (hp : valid p) : valid (neg p) := hp

theorem valid_mul (p q : WholeBi) (hp : valid p) (hq : valid q) : valid (mul p q) :=
  Int.mul_pos hp hq

theorem valid_pow (p : WholeBi) (n : Nat) (hp : valid p) : valid (pow p n) := by
  exact pow_pos hp n

theorem recover_constant (a : Rat) : recover (constant a) = [[a]] := by
  simp only [recover, constant, IBi.castRat, IUni.castRat, List.map_cons,
    List.map_nil, rscale, Uni.scale, Int.cast_natCast]
  congr 2
  simpa only [one_div, div_eq_mul_inv, mul_comm, mul_one] using Rat.num_div_den a

theorem recover_add (p q : WholeBi) (hp : valid p) (hq : valid q) :
    recover (add p q) = Bi.add (recover p) (recover q) := by
  have hd1 : (p.den : Rat) ≠ 0 := by exact_mod_cast (ne_of_gt hp)
  have hd2 : (q.den : Rat) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  simp only [recover, add, Int.cast_mul, IBi.castRat_add, IBi.castRat_scale,
    rscale_add, rscale_scale]
  congr 1 <;> congr 1 <;> field_simp [hd1, hd2]

theorem recover_neg (p : WholeBi) : recover (neg p) = Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.neg (recover p) := by
  simp only [recover, neg, IBi.castRat_neg]
  rw [neg_scaled]

theorem recover_mul (p q : WholeBi) :
    recover (mul p q) = Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.mul (recover p) (recover q) := by
  simp only [recover, mul, IBi.castRat_mul, Int.cast_mul, mul_scaled]
  congr 1
  simp only [one_div, mul_inv_rev, mul_comm]

theorem recover_pow (p : WholeBi) (n : Nat) :
    recover (pow p n) = Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.pow (recover p) n := by
  simp only [recover, pow, IBi.castRat_pow, Int.cast_pow, pow_scaled]
  congr 1
  simp only [one_div, inv_pow]

def encode : Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr → WholeBi → WholeBi → WholeBi
  | .constant a, _, _ => constant a
  | .first, x, _ => x
  | .second, _, y => y
  | .add a b, x, y => add (encode a x y) (encode b x y)
  | .neg a, x, y => neg (encode a x y)
  | .mul a b, x, y => mul (encode a x y) (encode b x y)
  | .pow a n, x, y => pow (encode a x y) n

theorem encode_valid (e : Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr) (x y : WholeBi) (hx : valid x) (hy : valid y) :
    valid (encode e x y) := by
  induction e with
  | constant a => exact valid_constant a
  | first => exact hx
  | second => exact hy
  | add a b ha hb => exact valid_add _ _ ha hb
  | neg a ha => exact valid_neg _ ha
  | mul a b ha hb => exact valid_mul _ _ ha hb
  | pow a n ha => exact valid_pow _ n ha

theorem encode_recover (e : Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr) (x y : WholeBi) (hx : valid x) (hy : valid y) :
    recover (encode e x y) = Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode e (recover x) (recover y) := by
  induction e with
  | constant a => exact recover_constant a
  | first => rfl
  | second => rfl
  | add a b ha hb =>
    rw [encode, recover_add _ _ (encode_valid a x y hx hy) (encode_valid b x y hx hy),
      ha, hb, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | neg a ha => rw [encode, recover_neg, ha, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | mul a b ha hb => rw [encode, recover_mul, ha, hb, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]
  | pow a n ha => rw [encode, recover_pow, ha, Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.encode]

theorem chart_eq_recover (e : Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr) (l h v w : Rat) (x y : WholeBi)
    (hx : valid x) (hy : valid y)
    (hxr : recover x = [[l],[h-l]]) (hyr : recover y = [[v,w-v]]) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.Expr.chart e l h v w = recover (encode e x y) := by
  rw [encode_recover e x y hx hy, hxr, hyr]
  rfl

end WholeBi
end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.BCFG.IBi.castRat_add
#print axioms Erdos993Lean.BCFG.IBi.castRat_scale
#print axioms Erdos993Lean.BCFG.IBi.castRat_mul
#print axioms Erdos993Lean.BCFG.IBi.castRat_pow
#print axioms Erdos993Lean.BCFG.IBi.castRat_tensor
#print axioms Erdos993Lean.BCFG.IBi.castRat_sumRange
#print axioms Erdos993Lean.BCFG.IBi.castRat_getD_getD
#print axioms Erdos993Lean.BCFG.IBi.castRat_trim
#print axioms Erdos993Lean.BCFG.IBi.checkEq_of_scaled
#print axioms Erdos993Lean.F4Fast.P04Int.trim_rscale
#print axioms Erdos993Lean.F4Fast.P04Int.WholeBi.encode_valid
#print axioms Erdos993Lean.F4Fast.P04Int.WholeBi.encode_recover
#print axioms Erdos993Lean.F4Fast.P04Int.WholeBi.chart_eq_recover
