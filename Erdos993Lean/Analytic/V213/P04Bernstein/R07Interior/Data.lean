module

public import Erdos993Lean.Analytic.V213.ZeroTiltLaplaceBernstein
public import Erdos993Lean.Analytic.V213.ZeroTiltLaplacePolynomialEncoding

/-! Printed row P04_BERNSTEIN_07.
No expanded coefficient vector is transcribed. chart/coeff are exact Lean
definitions; degree bounds are validated by the later full identity check.
Univariate rows use a dummy[0,1] second chart with m=0. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior

open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial Erdos993Lean.BCFG

def n : Nat := 9
def m : Nat := 6
def lo : Rat := (3/7)
def hi : Rat := (7/10)
def v : Rat := (0)
def w : Rat := (1/2)
def expr : Expr := interiorExpr (3/1250)
def lower : List Rat := [229, 304, 386, 471, 555, 634, 703, 760, 800, 823]
def chart : Bi := Expr.chart expr lo hi v w
def coeff : Nat → Nat → Rat := bernCoefficient n m chart

end Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior

#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.n
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.n
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.m
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.m
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.lo
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.lo
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.hi
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.hi
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.v
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.v
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.w
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.w
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.expr
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.expr
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.lower
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.lower
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.chart
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.chart
#check Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.coeff
#print axioms Erdos993Lean.Analytic.V213.P04Bernstein.R07Interior.coeff
