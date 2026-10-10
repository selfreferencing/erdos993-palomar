module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_10.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 6
def m : Nat := 6
def lo : Rat := (3/7)
def hi : Rat := (7/10)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := leafSlopeExpr (3/1250)
def lower : List Rat := [69, 144, 241, 355, 474, 578, 632]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope

#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R10LeafSlope.coeff
