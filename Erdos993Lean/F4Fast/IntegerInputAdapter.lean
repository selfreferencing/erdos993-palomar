module

public import Erdos993Lean.F4Fast.IntegerNormalization
public import Mathlib.Data.List.GetD

/-!
Generic source-exact adapters for integer polynomial certificates. Rational
inputs are connected to integer computations through field identities. Matrix
coefficients use their original literal numerator/denominator shape and bounded
integer cross-product guards; no large rational equality is decided here.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG
namespace IUni

theorem composition_eq_integer (p : Uni) (P : IUni) (a b : Rat)
    (A B D : Int) (M : Nat) (C : IUni)
    (hp : p = castRat P) (hlen : P.length ≤ M+1) (hD : D ≠ 0)
    (ha : a = (A : Rat)/(D : Rat)) (hb : b = (B : Rat)/(D : Rat))
    (hcalc : affineHom P A B D M = C) :
    Uni.comp p [a,b] =
      Uni.scale ((1 : Rat)/((D^M : Int) : Rat)) (castRat C) := by
  have hd : (D : Rat) ≠ 0 := by exact_mod_cast hD
  rw [hp, ha, hb, affineHom_cast P A B D M hlen hd, hcalc]
  simp only [Int.cast_pow, one_div]

theorem outer_eq_integer (N k : Nat) (qc rq : Rat) (Q R D : Int) (W : IUni)
    (hk : k ≤ N) (hD : D ≠ 0)
    (hqc : qc = (Q : Rat)/(D : Rat)) (hrq : rq = (R : Rat)/(D : Rat))
    (hcalc : mul (pow [Q,R] k) (pow [D-Q,-R] (N-k)) = W) :
    Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) =
      Uni.scale ((1 : Rat)/((D^N : Int) : Rat)) (castRat W) := by
  have hd : (D : Rat) ≠ 0 := by exact_mod_cast hD
  have hq : [qc,rq] = Uni.scale ((D : Rat)⁻¹) (castRat [Q,R]) := by
    rw [hqc, hrq]
    simp only [castRat, List.map_cons, List.map_nil, Uni.scale,
      div_eq_mul_inv, mul_comm]
  have hc : [1-qc,-rq] =
      Uni.scale ((D : Rat)⁻¹) (castRat [D-Q,-R]) := by
    rw [hqc, hrq]
    simp only [castRat, List.map_cons, List.map_nil, Int.cast_sub,
      Int.cast_neg, Uni.scale]
    congr 2 <;> field_simp [hd] <;> ring
  rw [hq, hc, rat_pow_scaled, rat_pow_scaled, rat_mul_scaled,
    ← castRat_mul, hcalc]
  have hs : ((D : Rat)⁻¹)^k * ((D : Rat)⁻¹)^(N-k) =
      (1 : Rat)/((D^N : Int) : Rat) := by
    rw [← pow_add, Nat.add_sub_of_le hk, inv_pow, one_div, Int.cast_pow]
  rw [hs]

def ratioRow (M : Nat) (nums dens : IUni) : Uni :=
  (List.range (M+1)).map (fun j =>
    (nums.getD j 0 : Rat)/(dens.getD j 1 : Rat))

def ratioMatrix (N M : Nat) (numrows denrows : List IUni) : Bi :=
  (List.range (N+1)).map (fun i =>
    ratioRow M (numrows.getD i []) (denrows.getD i []))

theorem ratioRow_getD (M : Nat) (nums dens : IUni) (j : Nat) (hj : j < M+1) :
    (ratioRow M nums dens).getD j 0 =
      (nums.getD j 0 : Rat)/(dens.getD j 1 : Rat) := by
  simp only [ratioRow, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hj, Option.map_some, Option.getD_some]

theorem ratioMatrix_getD (N M : Nat) (numrows denrows : List IUni)
    (i : Nat) (hi : i < N+1) :
    (ratioMatrix N M numrows denrows).getD i [] =
      ratioRow M (numrows.getD i []) (denrows.getD i []) := by
  simp only [ratioMatrix, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

theorem ratioMatrix_getD_getD (N M : Nat) (numrows denrows : List IUni)
    (i j : Nat) (hi : i < N+1) (hj : j < M+1) :
    ((ratioMatrix N M numrows denrows).getD i []).getD j 0 =
      ((numrows.getD i []).getD j 0 : Rat)/
        ((denrows.getD i []).getD j 1 : Rat) := by
  rw [ratioMatrix_getD N M numrows denrows i hi, ratioRow_getD M _ _ j hj]

/-- One source-shape equality and integer guards produce the coefficient
premise consumed by the original bounded Bernstein row checker. -/
theorem ratioMatrix_row_coeffs (N M : Nat) (A : Bi)
    (numrows denrows : List IUni) (Z : IUni) (DA : Int) (i : Nat)
    (hi : i < N+1) (hshape : A = ratioMatrix N M numrows denrows)
    (hDA : DA ≠ 0)
    (hdens : ∀ j < M+1, (denrows.getD i []).getD j 1 ≠ 0)
    (hcross : ∀ j < M+1,
      (numrows.getD i []).getD j 0 * DA =
        Z.getD j 0 * (denrows.getD i []).getD j 1) :
    ∀ j < M+1, (A.getD i []).getD j 0 = (Z.getD j 0 : Rat)/(DA : Rat) := by
  intro j hj
  rw [hshape, ratioMatrix_getD_getD N M numrows denrows i j hi hj]
  exact fractional_clear _ _ _ DA (hdens j hj) hDA (hcross j hj)

end IUni
end Erdos993Lean.BCFG

#print axioms Erdos993Lean.BCFG.IUni.composition_eq_integer
#print axioms Erdos993Lean.BCFG.IUni.outer_eq_integer
#print axioms Erdos993Lean.BCFG.IUni.ratioRow_getD
#print axioms Erdos993Lean.BCFG.IUni.ratioMatrix_getD
#print axioms Erdos993Lean.BCFG.IUni.ratioMatrix_getD_getD
#print axioms Erdos993Lean.BCFG.IUni.ratioMatrix_row_coeffs
