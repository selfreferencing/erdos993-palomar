module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_05.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 6
def lo : Rat := (1/4)
def hi : Rat := (3/7)
def v : Rat := (0)
def w : Rat := (1/2)
def expr : Expr := interiorExpr (-1/125)
def lower : List Rat := [111, 121, 135, 155, 180, 209, 244, 282, 324, 368]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R05Interior.coeff
