module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_03.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 0
def lo : Rat := (1/4)
def hi : Rat := (3/7)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := leafExpr (-1/125)
def lower : List Rat := [6683, 7003, 7414, 7913, 8492, 9137, 9827, 10538, 11239, 11895]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf

#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R03Leaf.coeff
