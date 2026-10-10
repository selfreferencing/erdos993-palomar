module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_02.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 8
def m : Nat := 0
def lo : Rat := (1/4)
def hi : Rat := (7/10)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := plusExpr (3/1250)
def lower : List Rat := [430, 633, 859, 1072, 1227, 1273, 1170, 910, 536]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus

#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R02Plus.coeff
