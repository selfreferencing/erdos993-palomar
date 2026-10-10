module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceExactBi
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialExpressions

/-! Literal syntax encodings of the five printed cleared polynomial formulas.
The proofs identify evaluation with the previously specified Real expressions.
No coefficient table is supplied or evaluated outside Lean. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

def minusExpr (d : Rat) : Expr :=
  let q := Expr.first
  let d := Expr.constant d;
  -100*q*(2-q)*(1-q)*(1+2*q)^2*(1+q-q^2)+
  q*(2-q)*(1+2*q)*(1+q-q^2)*(1+3*q)*(1+2*q+q*(1+q))+
  q^2*(2-q)*(1+2*q)^2*(100*(1-q)-(1+3*q))+
  (2-q)*(1+2*q)^2*(1+q-q^2)*(1+3*q)+
  200*q*(1+2*q)*(1-q)^2*(1+q-q^2)*(1+q)+
  100*d*(2-q)*(1-q)*(1+q-q^2)*(1+q)^2

def plusExpr (d : Rat) : Expr :=
  let q := Expr.first;
  -minusExpr d+(2-q)*(1+2*q)*(1+q-q^2)*(1+3*q)*(1+q)^2

def leafExpr (d : Rat) : Expr :=
  let q := Expr.first
  let d := Expr.constant d
  4*q*(2-q)*(1-q)*(1+q)*(1+q-q^2)*(100*(1-q)-(1+3*q))*(3*(2+q)^2+q^2)-
  3*(1+3*q)*q^2*(2-q)^2*(1+q)*(2+q)^3-
  1200*q*(1+2*q)*(1-q)^3*(2+q)^3-
  600*d*(2-q)*(1-q)^2*(1+q)*(2+q)^3

def interiorExpr (d : Rat) : Expr :=
  let q := Expr.first
  let u := Expr.second
  let d := Expr.constant d
  q*(1+q)^2*(2-q)*((101+3*q)*(1-q)^2+q*(1+3*q)*(2-q)*u^2)*(1+q*u^2)^2-
  (100*q*(1-q)^2*(2+q)*(1+2*q)+50*d*(1-q)*(1+q)*(2-q)*(2+q))*
    (1-q+q*u^2)*(1+q*u+q*u^2-q*u^3)

def leafSlopeExpr (d : Rat) : Expr :=
  let q := Expr.first
  let u := Expr.second
  let d := Expr.constant d
  q*(1+q)*(100-101*q-3*q^2+q*(1+3*q)*u^2)*(1+q*u^2)^2-
  (100*q*(1+2*q)*(1-q)+50*d*(1+q)*(2-q))*(1-q+q*u^2)*(1+q*u+q*u^2-q*u^3)

theorem minusExpr_sound (d : Rat) (q u : ℝ) :
    Expr.eval (minusExpr d) q u=PolynomialExpression.minus q (d : ℝ) := by
  have eval_sub (a b : Expr) :
      Expr.eval (a - b) q u = Expr.eval a q u - Expr.eval b q u := by
    change Expr.eval a q u + -(Expr.eval b q u) = _
    exact (sub_eq_add_neg _ _).symm
  have eval_pow (a : Expr) (n : Nat) :
      Expr.eval (a ^ n) q u = (Expr.eval a q u) ^ n := by rfl
  norm_num [minusExpr,Expr.eval,PolynomialExpression.minus,eval_sub,eval_pow] <;> ring

theorem plusExpr_sound (d : Rat) (q u : ℝ) :
    Expr.eval (plusExpr d) q u=PolynomialExpression.plus q (d : ℝ) := by
  have eval_sub (a b : Expr) :
      Expr.eval (a - b) q u = Expr.eval a q u - Expr.eval b q u := by
    change Expr.eval a q u + -(Expr.eval b q u) = _
    exact (sub_eq_add_neg _ _).symm
  have eval_pow (a : Expr) (n : Nat) :
      Expr.eval (a ^ n) q u = (Expr.eval a q u) ^ n := by rfl
  norm_num [plusExpr,minusExpr,Expr.eval,PolynomialExpression.plus,PolynomialExpression.minus,eval_sub,eval_pow] <;> ring

theorem leafExpr_sound (d : Rat) (q u : ℝ) :
    Expr.eval (leafExpr d) q u=PolynomialExpression.leaf q (d : ℝ) := by
  have eval_sub (a b : Expr) :
      Expr.eval (a - b) q u = Expr.eval a q u - Expr.eval b q u := by
    change Expr.eval a q u + -(Expr.eval b q u) = _
    exact (sub_eq_add_neg _ _).symm
  have eval_pow (a : Expr) (n : Nat) :
      Expr.eval (a ^ n) q u = (Expr.eval a q u) ^ n := by rfl
  norm_num [leafExpr,Expr.eval,PolynomialExpression.leaf,eval_sub,eval_pow] <;> ring

theorem interiorExpr_sound (d : Rat) (q u : ℝ) :
    Expr.eval (interiorExpr d) q u=PolynomialExpression.interior q u (d : ℝ) := by
  have eval_sub (a b : Expr) :
      Expr.eval (a - b) q u = Expr.eval a q u - Expr.eval b q u := by
    change Expr.eval a q u + -(Expr.eval b q u) = _
    exact (sub_eq_add_neg _ _).symm
  have eval_pow (a : Expr) (n : Nat) :
      Expr.eval (a ^ n) q u = (Expr.eval a q u) ^ n := by rfl
  norm_num [interiorExpr,Expr.eval,PolynomialExpression.interior,eval_sub,eval_pow] <;> ring

theorem leafSlopeExpr_sound (d : Rat) (q u : ℝ) :
    Expr.eval (leafSlopeExpr d) q u=PolynomialExpression.leafSlope q u (d : ℝ) := by
  have eval_sub (a b : Expr) :
      Expr.eval (a - b) q u = Expr.eval a q u - Expr.eval b q u := by
    change Expr.eval a q u + -(Expr.eval b q u) = _
    exact (sub_eq_add_neg _ _).symm
  have eval_pow (a : Expr) (n : Nat) :
      Expr.eval (a ^ n) q u = (Expr.eval a q u) ^ n := by rfl
  norm_num [leafSlopeExpr,Expr.eval,PolynomialExpression.leafSlope,eval_sub,eval_pow] <;> ring

end Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.minusExpr_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.minusExpr_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.plusExpr_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.plusExpr_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.leafExpr_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.leafExpr_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.interiorExpr_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.interiorExpr_sound
#check Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.leafSlopeExpr_sound
#print axioms Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial.leafSlopeExpr_sound
