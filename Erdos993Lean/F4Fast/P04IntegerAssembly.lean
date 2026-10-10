module

public import Erdos993Lean.F4Fast.P04IntegerExpr
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein

/-! Bounded exact recovery of the original Bernstein coefficient-list
assembly. The only finite premise is an integer trailing-zero list check;
coefficient fractions are recovered using symbolic field laws.
-/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Bi

theorem sumRange_congr (f g : Nat → Bi) (n : Nat)
    (h : ∀ j < n, f j = g j) : sumRange f n = sumRange g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumRange, sumRange, ih (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self n))),
      h n (Nat.lt_succ_self n)]

end Erdos993Lean.BCFG.Bi

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

def integerBernPoly (m : Nat) (C : Nat → Int) : IUni :=
  IUni.sumRange (fun B => IUni.scale (C B) (IUni.bernBasis m B)) (m+1)

def integerFromBernstein (n m : Nat) (C : Nat → Nat → Int) : IBi :=
  IBi.sumRange (fun A => IBi.tensor (IUni.bernBasis n A)
    (integerBernPoly m (C A))) (n+1)

theorem bernPoly_eq_integer (m : Nat) (b : Nat → Rat) (C : Nat → Int) (D : Int)
    (hb : ∀ B < m+1, b B = (C B : Rat)/(D : Rat)) :
    Uni.bernPoly m b = Uni.scale (1/(D : Rat)) (IUni.castRat (integerBernPoly m C)) := by
  unfold Uni.bernPoly integerBernPoly
  rw [IUni.castRat_sumRange, IUni.rat_scale_sumRange]
  apply Uni.sumRange_congr
  intro B hB
  rw [hb B hB, IUni.castRat_scale, IUni.castRat_bernBasis, IUni.rat_scale_scale]
  congr 1
  simp only [div_eq_mul_inv, one_mul, mul_one]
  exact mul_comm _ _

theorem fromBernstein_eq_integer (n m : Nat) (b : Nat → Nat → Rat)
    (C : Nat → Nat → Int) (D : Int)
    (hb : ∀ A < n+1, ∀ B < m+1, b A B = (C A B : Rat)/(D : Rat)) :
    Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.fromBernstein n m b =
      rscale (1/(D : Rat)) (IBi.castRat (integerFromBernstein n m C)) := by
  unfold Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.fromBernstein
    integerFromBernstein
  rw [IBi.castRat_sumRange, rscale_sumRange]
  apply Bi.sumRange_congr
  intro A hA
  rw [bernPoly_eq_integer m (b A) (C A) D (hb A hA), IBi.castRat_tensor,
    IUni.castRat_bernBasis]
  simpa only [one_mul, uni_scale_one] using tensor_scaled 1 (1/(D : Rat))
    (Uni.bernBasis n A) (IUni.castRat (integerBernPoly m (C A)))

end Erdos993Lean.F4Fast.P04Int

namespace Erdos993Lean.BCFG.IBi
open Erdos993Lean.F4Fast.P04Int

/-- Cancel the common chart denominator symbolically. The finite checker
compares only scale W p and q, so its integer numerals contain no extra D. -/
theorem checkEq_of_common_scale (D W : Int) (hD : D ≠ 0) (hW : W ≠ 0)
    (p q : IBi) (h : checkEq (scale W p) q = true) :
    Bi.checkEq (rscale (1/(D : Rat)) (castRat p))
      (rscale (1/((D*W : Int) : Rat)) (castRat q)) = true := by
  have hd : (D : Rat) ≠ 0 := by exact_mod_cast hD
  have hw : (W : Rat) ≠ 0 := by exact_mod_cast hW
  have ht : trim (scale W p) = trim q := of_decide_eq_true h
  have hr := congrArg castRat ht
  rw [castRat_trim, castRat_trim, castRat_scale, trim_rscale _ hw] at hr
  let s : Rat := 1/((D : Rat)*(W : Rat))
  have he := congrArg (rscale s) hr
  rw [rscale_scale] at he
  have hleft : s*(W : Rat) = 1/(D : Rat) := by
    dsimp [s]
    field_simp [hd, hw]
  rw [hleft] at he
  have hs : s ≠ 0 := div_ne_zero one_ne_zero (mul_ne_zero hd hw)
  unfold Bi.checkEq
  simp only [Int.cast_mul]
  change decide (Bi.trim (rscale (1/(D : Rat)) (castRat p)) =
    Bi.trim (rscale s (castRat q))) = true
  rw [trim_rscale _ (div_ne_zero one_ne_zero hd), trim_rscale _ hs, he]
  simp

end Erdos993Lean.BCFG.IBi

namespace Erdos993Lean.F4Fast.P04Int
open Erdos993Lean.BCFG

theorem reconstruction_of_integer (n m : Nat) (chart : Bi)
    (b : Nat → Nat → Rat) (Z : IBi) (C : Nat → Nat → Int) (D W : Int)
    (hD : D ≠ 0) (hW : W ≠ 0)
    (hchart : chart = rscale (1/(D : Rat)) (IBi.castRat Z))
    (hb : ∀ A < n+1, ∀ B < m+1, b A B = (C A B : Rat)/((D*W : Int) : Rat))
    (hclear : IBi.checkEq (IBi.scale W Z) (integerFromBernstein n m C) = true) :
    Bi.checkEq chart
      (Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.fromBernstein n m b) = true := by
  rw [hchart, fromBernstein_eq_integer n m b C (D*W) hb]
  exact IBi.checkEq_of_common_scale D W hD hW Z (integerFromBernstein n m C) hclear

end Erdos993Lean.F4Fast.P04Int

#print axioms Erdos993Lean.BCFG.Bi.sumRange_congr
#print axioms Erdos993Lean.F4Fast.P04Int.bernPoly_eq_integer
#print axioms Erdos993Lean.F4Fast.P04Int.fromBernstein_eq_integer
#print axioms Erdos993Lean.BCFG.IBi.checkEq_of_common_scale
#print axioms Erdos993Lean.F4Fast.P04Int.reconstruction_of_integer
