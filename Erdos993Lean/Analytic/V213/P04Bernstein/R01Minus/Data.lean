module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_01.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 8
def m : Nat := 0
def lo : Rat := (1/4)
def hi : Rat := (7/10)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := minusExpr (-1/125)
def lower : List Rat := [168, 179, 209, 294, 476, 799, 1291, 1946, 2703]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus

#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R01Minus.coeff
