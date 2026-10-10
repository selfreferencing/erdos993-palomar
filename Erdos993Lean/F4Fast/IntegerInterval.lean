module

public import Erdos993Lean.F4Fast.IntegerInputAdapter
public import Erdos993Lean.BCFG.Certificate

/-! Exact source-list adapters for the original interval identity predicate.
Integer component and cross-product hypotheses are finite proof obligations;
none are assumed as axioms. Every list shape and trailing zero is retained. -/

@[expose] public section

set_option autoImplicit false

namespace Erdos993Lean.BCFG

namespace Uni

/-- Scalar multiplication commutes with the exact original list composition,
including the empty input and multiplication's structural zero padding. -/
theorem comp_scale (s : Rat) (p q : Uni) :
    comp (scale s p) q = scale s (comp p q) := by
  induction p with
  | nil => rfl
  | cons a p ih =>
      change add [s*a] (mul q (comp (scale s p) q)) =
        scale s (add [a] (mul q (comp p q)))
      rw [ih, IUni.rat_mul_scale_right, IUni.rat_scale_add]
      rfl

end Uni

namespace IUni

/-- Bounded coefficient reconstruction from the unchanged source fraction
list and checked integer cross-products; no Rat equality is decided. -/
theorem ratioRow_coeffs (M : Nat) (c : Uni) (nums dens Z : IUni) (D : Int)
    (hshape : c = ratioRow M nums dens) (hD : D ≠ 0)
    (hdens : ∀ j < M+1, dens.getD j 1 ≠ 0)
    (hcross : ∀ j < M+1, nums.getD j 0 * D = Z.getD j 0 * dens.getD j 1) :
    ∀ j < M+1, c.getD j 0 = (Z.getD j 0 : Rat)/(D : Rat) := by
  intro j hj
  rw [hshape, ratioRow_getD M nums dens j hj]
  exact fractional_clear _ _ _ D (hdens j hj) hD (hcross j hj)

end IUni

namespace Uni

/-- General composition predicate recovered through guarded integer clearing.
The rational polynomial lists are unchanged, not replaced by evaluations. -/
theorem checkEq_comp_of_integer_clear (p q : Uni) (a b : Rat) (P C Q : IUni)
    (DL DChart DI : Int) (hDL : DL ≠ 0) (hDChart : DChart ≠ 0) (hDI : DI ≠ 0)
    (hL : p = scale ((1 : Rat)/(DL : Rat)) (IUni.castRat P))
    (hC : comp (IUni.castRat P) [a,b] =
      scale ((1 : Rat)/(DChart : Rat)) (IUni.castRat C))
    (hT : q = scale ((1 : Rat)/(DI : Rat)) (IUni.castRat Q))
    (hclear : IUni.checkEq (IUni.scale DI C) (IUni.scale (DL*DChart) Q) = true) :
    checkEq (comp p [a,b]) q = true := by
  rw [hL, comp_scale, hC, IUni.rat_scale_scale, hT]
  exact IUni.checkEq_of_cleared DL DChart DI hDL hDChart hDI C Q hclear

/-- Exact original interval-identity type. The chart is the original
[I.lo, I.hi-I.lo], and the target is its original Bernstein coefficient list. -/
theorem interval_identity_of_integer_clear (M : Nat) (lower : Uni)
    (I : IntervalCertificate) (P C Q : IUni) (DL DChart DI : Int)
    (hDL : DL ≠ 0) (hDChart : DChart ≠ 0) (hDI : DI ≠ 0)
    (hLbern : bernVector M lower =
      scale ((1 : Rat)/(DL : Rat)) (IUni.castRat P))
    (hChart : comp (IUni.castRat P) [I.lo,I.hi-I.lo] =
      scale ((1 : Rat)/(DChart : Rat)) (IUni.castRat C))
    (hTbern : bernVector M I.coeffs =
      scale ((1 : Rat)/(DI : Rat)) (IUni.castRat Q))
    (hclear : IUni.checkEq (IUni.scale DI C) (IUni.scale (DL*DChart) Q) = true) :
    checkEq
      (comp (bernVector M lower) [I.lo,I.hi-I.lo])
      (bernVector M I.coeffs) = true := by
  exact checkEq_comp_of_integer_clear (bernVector M lower) (bernVector M I.coeffs)
    I.lo (I.hi-I.lo) P C Q DL DChart DI hDL hDChart hDI hLbern hChart hTbern hclear

end Uni

end Erdos993Lean.BCFG

#print axioms Erdos993Lean.BCFG.Uni.comp_scale
#print axioms Erdos993Lean.BCFG.IUni.ratioRow_coeffs
#print axioms Erdos993Lean.BCFG.Uni.checkEq_comp_of_integer_clear
#print axioms Erdos993Lean.BCFG.Uni.interval_identity_of_integer_clear
