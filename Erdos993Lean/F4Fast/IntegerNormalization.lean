module

public import Erdos993Lean.F4Fast.IntegerPolynomial

/-!
Exact integer-list bridges for the original normalization and Bernstein row
checks. Every component hypothesis is equality of the original coefficient
list, and the final consumer uses the original trailing-zero trim semantics.
The cleared integer check retains arbitrary list lengths; no equal-length or
semantic polynomial-evaluation premise replaces the original checker.
-/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

namespace IUni

def cachedNormalizedRow (N : Nat) (CZ WZ : List IUni) (i : Nat) : IUni :=
  sumRange (fun k => scale ((WZ.getD k []).getD i 0) (CZ.getD k [])) (N+1)

def cachedBernVector (M : Nat) (HZ : List IUni) (Z : IUni) : IUni :=
  sumRange (fun j => scale (Z.getD j 0) (HZ.getD j [])) (M+1)

/-- The recursion is identical to the original rational trailing-zero trim. -/
def trim : IUni → IUni
  | [] => []
  | a :: p =>
      let t := trim p
      if a = 0 ∧ t = [] then [] else a :: t

def checkEq (p q : IUni) : Bool := decide (trim p = trim q)

theorem rat_scale_getD (s : Rat) (p : Uni) (i : Nat) :
    (Uni.scale s p).getD i 0 = s * p.getD i 0 := by
  induction p generalizing i with
  | nil => simp [Uni.scale]
  | cons a p ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simpa only [Uni.scale, List.getD_cons_succ] using ih i

theorem castRat_trim (p : IUni) : castRat (trim p) = Uni.trim (castRat p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change castRat (if a = 0 ∧ trim p = [] then [] else a :: trim p) =
        (if (a : Rat) = 0 ∧ Uni.trim (castRat p) = [] then []
          else (a : Rat) :: Uni.trim (castRat p))
      rw [← ih]
      have hzero : ((a : Rat) = 0) ↔ a = 0 := Int.cast_eq_zero
      have hnil : castRat (trim p) = [] ↔ trim p = [] := by simp [castRat]
      simp only [hzero, hnil]
      split_ifs <;> rfl

theorem rat_trim_scale (s : Rat) (hs : s ≠ 0) (p : Uni) :
    Uni.trim (Uni.scale s p) = Uni.scale s (Uni.trim p) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change (if s*a = 0 ∧ Uni.trim (Uni.scale s p) = [] then []
          else (s*a) :: Uni.trim (Uni.scale s p)) =
        Uni.scale s (if a = 0 ∧ Uni.trim p = [] then [] else a :: Uni.trim p)
      rw [ih]
      have hzero : s*a = 0 ↔ a = 0 := by simp [hs]
      have hnil : Uni.scale s (Uni.trim p) = [] ↔ Uni.trim p = [] := by
        cases Uni.trim p <;> simp [Uni.scale]
      simp only [hzero, hnil]
      split_ifs <;> rfl

theorem checkEq_castRat (p q : IUni) (h : checkEq p q = true) :
    Uni.checkEq (castRat p) (castRat q) = true := by
  have ht : trim p = trim q := of_decide_eq_true h
  have hc := congrArg castRat ht
  rw [castRat_trim, castRat_trim] at hc
  simp [Uni.checkEq, hc]

/-- Fraction equality follows from a guarded integer cross-product equality;
the proof applies field laws without evaluating numerical rational fractions. -/
theorem fractional_clear (n d Z D : Int) (hd : d ≠ 0) (hD : D ≠ 0)
    (hcross : n*D = Z*d) : (n : Rat)/(d : Rat) = (Z : Rat)/(D : Rat) := by
  have hdRat : (d : Rat) ≠ 0 := by exact_mod_cast hd
  have hDRat : (D : Rat) ≠ 0 := by exact_mod_cast hD
  apply (div_eq_div_iff hdRat hDRat).2
  exact_mod_cast hcross

/-- Integer cross-multiplication recovers precisely the rational list checker.
The explicit nonzero denominators justify every trim/scale commute. -/
theorem checkEq_of_cleared (DC DW DA : Int)
    (hDC : DC ≠ 0) (hDW : DW ≠ 0) (hDA : DA ≠ 0) (P Q : IUni)
    (hclear : checkEq (scale DA P) (scale (DC*DW) Q) = true) :
    Uni.checkEq
      (Uni.scale (((1 : Rat)/(DC : Rat))*((1 : Rat)/(DW : Rat))) (castRat P))
      (Uni.scale ((1 : Rat)/(DA : Rat)) (castRat Q)) = true := by
  have hc : (DC : Rat) ≠ 0 := by exact_mod_cast hDC
  have hw : (DW : Rat) ≠ 0 := by exact_mod_cast hDW
  have ha : (DA : Rat) ≠ 0 := by exact_mod_cast hDA
  have ht : trim (scale DA P) = trim (scale (DC*DW) Q) := of_decide_eq_true hclear
  have hr := congrArg castRat ht
  rw [castRat_trim, castRat_trim, castRat_scale, castRat_scale] at hr
  simp only [Int.cast_mul] at hr
  rw [rat_trim_scale (DA : Rat) ha,
    rat_trim_scale ((DC : Rat)*(DW : Rat)) (mul_ne_zero hc hw)] at hr
  let s : Rat := (1 : Rat)/((DA : Rat)*((DC : Rat)*(DW : Rat)))
  have hscaled := congrArg (Uni.scale s) hr
  rw [rat_scale_scale, rat_scale_scale] at hscaled
  have hleft : s*(DA : Rat) = ((1 : Rat)/(DC : Rat))*((1 : Rat)/(DW : Rat)) := by
    dsimp [s]
    field_simp [hc, hw, ha] <;> ring
  have hright : s*((DC : Rat)*(DW : Rat)) = (1 : Rat)/(DA : Rat) := by
    dsimp [s]
    field_simp [hc, hw, ha] <;> ring
  rw [hleft, hright] at hscaled
  have hn : ((1 : Rat)/(DC : Rat))*((1 : Rat)/(DW : Rat)) ≠ 0 :=
    mul_ne_zero (div_ne_zero one_ne_zero hc) (div_ne_zero one_ne_zero hw)
  have hb : (1 : Rat)/(DA : Rat) ≠ 0 := div_ne_zero one_ne_zero ha
  have htrim :
      Uni.trim (Uni.scale (((1 : Rat)/(DC : Rat))*((1 : Rat)/(DW : Rat))) (castRat P)) =
        Uni.trim (Uni.scale ((1 : Rat)/(DA : Rat)) (castRat Q)) := by
    rw [rat_trim_scale _ hn, rat_trim_scale _ hb]
    exact hscaled
  unfold Uni.checkEq
  rw [htrim] <;> simp

end IUni

namespace Bi

theorem normalizedRow_eq_intCached (N : Nat) (p : Bi) (qc rq a b : Rat)
    (CZ WZ : List IUni) (sc sw : Rat) (i : Nat)
    (hC : ∀ k < N+1, Uni.comp (p.getD k []) [a,b] =
      Uni.scale sc (IUni.castRat (CZ.getD k [])))
    (hW : ∀ k < N+1,
      Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) =
        Uni.scale sw (IUni.castRat (WZ.getD k []))) :
    normalizedRow N p qc rq a b i =
      Uni.scale (sc*sw) (IUni.castRat (IUni.cachedNormalizedRow N CZ WZ i)) := by
  unfold normalizedRow IUni.cachedNormalizedRow
  rw [IUni.castRat_sumRange, IUni.rat_scale_sumRange]
  apply Uni.sumRange_congr
  intro k hk
  rw [hC k hk, hW k hk, IUni.rat_scale_getD, IUni.castRat_getD,
    IUni.castRat_scale, IUni.rat_scale_scale, IUni.rat_scale_scale]
  congr 1
  ring

end Bi

namespace Uni

theorem bernVector_eq_intCached (M : Nat) (A : Uni)
    (HZ : List IUni) (Z : IUni) (sa : Rat)
    (hH : ∀ j < M+1, bernBasis M j = IUni.castRat (HZ.getD j []))
    (hA : ∀ j < M+1, A.getD j 0 = sa * (Z.getD j 0 : Rat)) :
    bernVector M A = Uni.scale sa (IUni.castRat (IUni.cachedBernVector M HZ Z)) := by
  unfold bernVector bernPoly IUni.cachedBernVector
  rw [IUni.castRat_sumRange, IUni.rat_scale_sumRange]
  apply sumRange_congr
  intro j hj
  dsimp only
  rw [hA j hj, hH j hj, IUni.castRat_scale, IUni.rat_scale_scale]

end Uni

namespace Bi

/-- Source-exact consumer of the checked integer cross-multiplication.
The coefficient relation is the original bounded Bernstein input domain. -/
theorem normalizedRow_checkEq_of_integer_clear (N M : Nat) (p : Bi) (Arow : Uni)
    (qc rq a b : Rat) (CZ WZ HZ : List IUni) (Zrow : IUni) (i : Nat)
    (DC DW DA : Int) (hDC : DC ≠ 0) (hDW : DW ≠ 0) (hDA : DA ≠ 0)
    (hC : ∀ k < N+1, Uni.comp (p.getD k []) [a,b] =
      Uni.scale ((1 : Rat)/(DC : Rat)) (IUni.castRat (CZ.getD k [])))
    (hW : ∀ k < N+1,
      Uni.mul (Uni.pow [qc,rq] k) (Uni.pow [1-qc,-rq] (N-k)) =
        Uni.scale ((1 : Rat)/(DW : Rat)) (IUni.castRat (WZ.getD k [])))
    (hH : ∀ j < M+1, Uni.bernBasis M j = IUni.castRat (HZ.getD j []))
    (hA : ∀ j < M+1, Arow.getD j 0 = (Zrow.getD j 0 : Rat)/(DA : Rat))
    (hclear : IUni.checkEq
      (IUni.scale DA (IUni.cachedNormalizedRow N CZ WZ i))
      (IUni.scale (DC*DW) (IUni.cachedBernVector M HZ Zrow)) = true) :
    Uni.checkEq (normalizedRow N p qc rq a b i) (Uni.bernVector M Arow) = true := by
  have hcoeff : ∀ j < M+1, Arow.getD j 0 =
      ((1 : Rat)/(DA : Rat)) * (Zrow.getD j 0 : Rat) := by
    intro j hj
    rw [hA j hj]
    simp only [div_eq_mul_inv, one_mul]
    exact mul_comm _ _
  rw [normalizedRow_eq_intCached N p qc rq a b CZ WZ
      ((1 : Rat)/(DC : Rat)) ((1 : Rat)/(DW : Rat)) i hC hW,
    Uni.bernVector_eq_intCached M Arow HZ Zrow ((1 : Rat)/(DA : Rat)) hH hcoeff]
  exact IUni.checkEq_of_cleared DC DW DA hDC hDW hDA _ _ hclear

end Bi

end Erdos993Lean.BCFG

#print axioms Erdos993Lean.BCFG.IUni.rat_scale_getD
#print axioms Erdos993Lean.BCFG.IUni.castRat_trim
#print axioms Erdos993Lean.BCFG.IUni.rat_trim_scale
#print axioms Erdos993Lean.BCFG.IUni.checkEq_castRat
#print axioms Erdos993Lean.BCFG.IUni.fractional_clear
#print axioms Erdos993Lean.BCFG.IUni.checkEq_of_cleared
#print axioms Erdos993Lean.BCFG.Bi.normalizedRow_eq_intCached
#print axioms Erdos993Lean.BCFG.Uni.bernVector_eq_intCached
#print axioms Erdos993Lean.BCFG.Bi.normalizedRow_checkEq_of_integer_clear
#check Erdos993Lean.BCFG.Bi.normalizedRow_checkEq_of_integer_clear
#print Erdos993Lean.BCFG.Bi.normalizedRow_checkEq_of_integer_clear
