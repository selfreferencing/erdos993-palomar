module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Chunk018

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 190: pow_succ.
def e0190 : Expr := Expr.pow e0002 4
def p0190 : Bi := exact_poly_nf_compact% (mul p0059 p0002)
theorem p0190_op : p0190 = mul p0059 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0190_encode : p0190 = Expr.encode e0190 [[0,1]] [[],[1]] := by
  rw [p0190_op]
  exact congrArg₂ mul p0059_encode p0002_encode

-- Source node 191: pow_succ.
def e0191 : Expr := Expr.pow e0002 5
def p0191 : Bi := exact_poly_nf_compact% (mul p0190 p0002)
theorem p0191_op : p0191 = mul p0190 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0191_encode : p0191 = Expr.encode e0191 [[0,1]] [[],[1]] := by
  rw [p0191_op]
  exact congrArg₂ mul p0190_encode p0002_encode

-- Source node 192: pow_succ.
def e0192 : Expr := Expr.pow e0002 6
def p0192 : Bi := exact_poly_nf_compact% (mul p0191 p0002)
theorem p0192_op : p0192 = mul p0191 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0192_encode : p0192 = Expr.encode e0192 [[0,1]] [[],[1]] := by
  rw [p0192_op]
  exact congrArg₂ mul p0191_encode p0002_encode

-- Source node 193: mul.
def e0193 : Expr := Expr.mul e0189 e0192
def p0193 : Bi := exact_poly_nf_compact% (mul p0189 p0192)
theorem p0193_op : p0193 = mul p0189 p0192 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0193_encode : p0193 = Expr.encode e0193 [[0,1]] [[],[1]] := by
  rw [p0193_op]
  exact congrArg₂ mul p0189_encode p0192_encode

-- Source node 194: mul.
def e0194 : Expr := Expr.mul e0193 e0006
def p0194 : Bi := exact_poly_nf_compact% (mul p0193 p0006)
theorem p0194_op : p0194 = mul p0193 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0194_encode : p0194 = Expr.encode e0194 [[0,1]] [[],[1]] := by
  rw [p0194_op]
  exact congrArg₂ mul p0193_encode p0006_encode

-- Source node 195: pow_zero.
def e0195 : Expr := Expr.pow e0001 0
def p0195 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0195_op : p0195 = ([[1]] : Bi) := by decide +kernel
theorem p0195_encode : p0195 = Expr.encode e0195 [[0,1]] [[],[1]] := by
  rw [p0195_op]
  rfl

-- Source node 196: pow_succ.
def e0196 : Expr := Expr.pow e0001 1
def p0196 : Bi := exact_poly_nf_compact% (mul p0195 p0001)
theorem p0196_op : p0196 = mul p0195 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0196_encode : p0196 = Expr.encode e0196 [[0,1]] [[],[1]] := by
  rw [p0196_op]
  exact congrArg₂ mul p0195_encode p0001_encode

-- Source node 197: pow_succ.
def e0197 : Expr := Expr.pow e0001 2
def p0197 : Bi := exact_poly_nf_compact% (mul p0196 p0001)
theorem p0197_op : p0197 = mul p0196 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0197_encode : p0197 = Expr.encode e0197 [[0,1]] [[],[1]] := by
  rw [p0197_op]
  exact congrArg₂ mul p0196_encode p0001_encode

-- Source node 198: mul.
def e0198 : Expr := Expr.mul e0194 e0197
def p0198 : Bi := exact_poly_nf_compact% (mul p0194 p0197)
theorem p0198_op : p0198 = mul p0194 p0197 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0198_encode : p0198 = Expr.encode e0198 [[0,1]] [[],[1]] := by
  rw [p0198_op]
  exact congrArg₂ mul p0194_encode p0197_encode

-- Source node 199: mul.
def e0199 : Expr := Expr.mul e0198 e0012
def p0199 : Bi := exact_poly_nf_compact% (mul p0198 p0012)
theorem p0199_op : p0199 = mul p0198 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0199_encode : p0199 = Expr.encode e0199 [[0,1]] [[],[1]] := by
  rw [p0199_op]
  exact congrArg₂ mul p0198_encode p0012_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0190
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0190
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0190_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0191
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0191
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0191_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0192
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0192
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0192_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0193
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0193
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0193_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0194
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0194
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0194_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0195
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0195
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0195_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0196
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0196
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0196_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0197
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0197
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0197_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0198
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0198
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0198_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0199
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0199
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0199_encode
