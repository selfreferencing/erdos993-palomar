module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_06.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 6
def lo : Rat := (1/4)
def hi : Rat := (3/7)
def v : Rat := (1/2)
def w : Rat := (1)
def expr : Expr := interiorExpr (-1/125)
def lower : List Rat := [72, 73, 79, 88, 102, 121, 145, 173, 205, 241]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R06Interior.coeff
