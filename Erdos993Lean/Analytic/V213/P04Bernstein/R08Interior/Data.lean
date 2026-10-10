module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_08.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 6
def lo : Rat := (3/7)
def hi : Rat := (7/10)
def v : Rat := (1/2)
def w : Rat := (1)
def expr : Expr := interiorExpr (3/1250)
def lower : List Rat := [62, 120, 187, 262, 346, 435, 529, 624, 701, 772]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R08Interior.coeff
