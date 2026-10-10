module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_09.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 6
def m : Nat := 6
def lo : Rat := (1/4)
def hi : Rat := (3/7)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := leafSlopeExpr (-1/125)
def lower : List Rat := [7, 11, 25, 51, 91, 144, 210]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope

#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R09LeafSlope.coeff
