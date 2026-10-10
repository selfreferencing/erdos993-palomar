module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightPolynomialDefs
public import Erdos993Lean.Analytic.V213.ResponseHalfLightDeterminantAlgebra

/-! Semantic interpretation of the exact polynomial syntax. These are
generic algebraic identities, before the physical rational substitution.
No finite coefficient equality or sign is asserted in this module. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

open ZeroTiltLaplace.FinitePolynomial

@[simp] theorem value_scalar (a : ℚ) (lam xi : ℝ) :
    Expr.eval (scalar a) lam xi=(a:ℝ) := rfl
@[simp] theorem value_nat (n : ℕ) (lam xi : ℝ) :
    Expr.eval (Expr.constant (n:ℚ)) lam xi=(n:ℝ) := by simp [Expr.eval]
@[simp] theorem value_add (e f : Bivariate) (lam xi : ℝ) :
    Expr.eval (e+f) lam xi=Expr.eval e lam xi+Expr.eval f lam xi := rfl
@[simp] theorem value_neg (e : Bivariate) (lam xi : ℝ) :
    Expr.eval (-e) lam xi= -Expr.eval e lam xi := rfl
@[simp] theorem value_sub (e f : Bivariate) (lam xi : ℝ) :
    Expr.eval (e-f) lam xi=Expr.eval e lam xi-Expr.eval f lam xi := rfl
@[simp] theorem value_mul (e f : Bivariate) (lam xi : ℝ) :
    Expr.eval (e*f) lam xi=Expr.eval e lam xi*Expr.eval f lam xi := rfl
@[simp] theorem value_pow (e : Bivariate) (n : ℕ) (lam xi : ℝ) :
    Expr.eval (e^n) lam xi=(Expr.eval e lam xi)^n := rfl
@[simp] theorem value_lam (lam xi : ℝ) : Expr.eval lamVar lam xi=lam := rfl
@[simp] theorem value_xi (lam xi : ℝ) : Expr.eval xiVar lam xi=xi := rfl

@[simp] theorem value_onePlus (lam xi : ℝ) : Expr.eval onePlus lam xi=1+lam := by
  simp [onePlus,Expr.eval]
@[simp] theorem value_factorC (lam xi : ℝ) : Expr.eval factorC lam xi=2-xi := by
  simp [factorC,Expr.eval]
@[simp] theorem value_factorD (lam xi : ℝ) : Expr.eval factorD lam xi=4+4*lam-lam*xi := by
  simp [factorD,Expr.eval]
@[simp] theorem value_factorE (lam xi : ℝ) : Expr.eval factorE lam xi=2+2*lam-(lam-1)*xi := by
  simp [factorE,Expr.eval,sub_eq_add_neg]
@[simp] theorem value_factorF (lam xi : ℝ) : Expr.eval factorF lam xi=2+4*lam+2*lam^2-lam^2*xi := by
  simp [factorF,Expr.eval]
@[simp] theorem value_factorG (lam xi : ℝ) : Expr.eval factorG lam xi=2+2*lam-lam*xi := by
  simp [factorG,Expr.eval]

theorem value_fieldPolynomial (i : Fin 4) (a b : ℤ) (lam xi : ℝ) :
    Expr.eval (fieldPolynomial i a b) lam xi=affineField i a b lam := by
  simp only [fieldPolynomial,value_add,value_mul,value_scalar,value_lam,
    Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_intCast,Rat.cast_ofNat]
  unfold affineField
  ring

theorem determinant_encoding_sound (r : Fin 8) (lam xi : ℝ) :
    evaluate lam xi (determinantPolynomial r)=Expr.eval (determinantExpression r) lam xi := by
  unfold evaluate determinantPolynomial
  rw [Expr.encode_sound]
  simp [BCFG.Bi.evalReal,BCFG.Uni.evalReal]

theorem unweighted_expression_sound (i : Fin 4) (phase : ℕ) (lam xi : ℝ) :
    Expr.eval (unweightedDeterminantPoly i phase) lam xi=
      determinantTenTerms lam (1+lam) (2-xi) (4+4*lam-lam*xi)
        (2+2*lam-(lam-1)*xi) (2+4*lam+2*lam^2-lam^2*xi)
        (2+2*lam-lam*xi) (Expr.eval (phaseDen phase) lam xi)
        (Expr.eval (correctionDen i phase) lam xi) xi
        (Expr.eval (a2Num i phase) lam xi) (Expr.eval (a1Num i phase) lam xi)
        (Expr.eval (baseANum i phase) lam xi) (Expr.eval (baseB i) lam xi)
        (Expr.eval (baseKNum i) lam xi) (Expr.eval upperRatioNum lam xi)
        (Expr.eval (gammaPoly i) lam xi) (Expr.eval (deltaPoly i) lam xi) := by
  simp only [unweightedDeterminantPoly,mixedKNum,mixedANum,
    value_add,value_sub,value_mul,value_pow,value_scalar,value_lam,value_xi,
    value_onePlus,value_factorC,value_factorD,value_factorE,value_factorF,value_factorG,
    determinantTenTerms]
  norm_num [Expr.eval]

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_scalar
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_scalar
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_nat
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_nat
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_add
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_add
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_neg
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_neg
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_sub
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_sub
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_mul
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_mul
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_pow
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_pow
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_lam
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_lam
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_xi
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_xi
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_onePlus
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_onePlus
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorC
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorC
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorD
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorD
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorE
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorE
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorF
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorF
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorG
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_factorG
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_fieldPolynomial
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.value_fieldPolynomial
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_encoding_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.determinant_encoding_sound
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.unweighted_expression_sound
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.unweighted_expression_sound
