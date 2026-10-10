module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_04.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 0
def lo : Rat := (3/7)
def hi : Rat := (7/10)
def v : Rat := (0)
def w : Rat := (1)
def expr : Expr := leafExpr (3/1250)
def lower : List Rat := [5343, 6775, 8119, 9244, 9994, 10184, 9618, 8099, 5463, 1636]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf

#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R04Leaf.coeff
