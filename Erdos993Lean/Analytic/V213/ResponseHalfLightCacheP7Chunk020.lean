module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP7Chunk019

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 200: mul.
def e0200 : Expr := Expr.mul e0196 e0199
def p0200 : Bi := exact_poly_nf_compact% (mul p0196 p0199)
theorem p0200_op : p0200 = mul p0196 p0199 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0200_encode : p0200 = Expr.encode e0200 [[0,1]] [[],[1]] := by
  rw [p0200_op]
  exact congrArg₂ mul p0196_encode p0199_encode

-- Source node 201: mul.
def e0201 : Expr := Expr.mul e0200 e0012
def p0201 : Bi := exact_poly_nf_compact% (mul p0200 p0012)
theorem p0201_op : p0201 = mul p0200 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0201_encode : p0201 = Expr.encode e0201 [[0,1]] [[],[1]] := by
  rw [p0201_op]
  exact congrArg₂ mul p0200_encode p0012_encode

-- Source node 202: mul.
def e0202 : Expr := Expr.mul e0201 e0019
def p0202 : Bi := exact_poly_nf_compact% (mul p0201 p0019)
theorem p0202_op : p0202 = mul p0201 p0019 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0202_encode : p0202 = Expr.encode e0202 [[0,1]] [[],[1]] := by
  rw [p0202_op]
  exact congrArg₂ mul p0201_encode p0019_encode

-- Source node 203: mul.
def e0203 : Expr := Expr.mul e0202 e0105
def p0203 : Bi := exact_poly_nf_compact% (mul p0202 p0105)
theorem p0203_op : p0203 = mul p0202 p0105 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0203_encode : p0203 = Expr.encode e0203 [[0,1]] [[],[1]] := by
  rw [p0203_op]
  exact congrArg₂ mul p0202_encode p0105_encode

-- Source node 204: mul.
def e0204 : Expr := Expr.mul e0203 e0004
def p0204 : Bi := exact_poly_nf_compact% (mul p0203 p0004)
theorem p0204_op : p0204 = mul p0203 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0204_encode : p0204 = Expr.encode e0204 [[0,1]] [[],[1]] := by
  rw [p0204_op]
  exact congrArg₂ mul p0203_encode p0004_encode

-- Source node 205: mul.
def e0205 : Expr := Expr.mul e0204 e0088
def p0205 : Bi := exact_poly_nf_compact% (mul p0204 p0088)
theorem p0205_op : p0205 = mul p0204 p0088 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0205_encode : p0205 = Expr.encode e0205 [[0,1]] [[],[1]] := by
  rw [p0205_op]
  exact congrArg₂ mul p0204_encode p0088_encode

-- Source node 206: neg.
def e0206 : Expr := Expr.neg e0205
def p0206 : Bi := exact_poly_nf_compact% (neg p0205)
theorem p0206_op : p0206 = neg p0205 := by decide +kernel
theorem p0206_encode : p0206 = Expr.encode e0206 [[0,1]] [[],[1]] := by
  rw [p0206_op]
  exact congrArg neg p0205_encode

-- Source node 207: add.
def e0207 : Expr := Expr.add e0189 e0206
def p0207 : Bi := exact_poly_nf_compact% (Bi.add p0189 p0206)
theorem p0207_op : p0207 = Bi.add p0189 p0206 := by decide +kernel
theorem p0207_encode : p0207 = Expr.encode e0207 [[0,1]] [[],[1]] := by
  rw [p0207_op]
  exact congrArg₂ Bi.add p0189_encode p0206_encode

-- Source node 208: constant.
def e0208 : Expr := Expr.constant ((1/320) : ℚ)
def p0208 : Bi := exact_poly_nf_compact% (([[((1/320) : ℚ)]] : Bi))
theorem p0208_op : p0208 = ([[((1/320) : ℚ)]] : Bi) := by decide +kernel
theorem p0208_encode : p0208 = Expr.encode e0208 [[0,1]] [[],[1]] := by
  rw [p0208_op]
  rfl

-- Source node 209: mul.
def e0209 : Expr := Expr.mul e0208 e0158
def p0209 : Bi := exact_poly_nf_compact% (mul p0208 p0158)
theorem p0209_op : p0209 = mul p0208 p0158 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0209_encode : p0209 = Expr.encode e0209 [[0,1]] [[],[1]] := by
  rw [p0209_op]
  exact congrArg₂ mul p0208_encode p0158_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0200
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0200
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0200_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0201
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0201
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0201_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0202
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0202
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0202_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0203
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0203
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0203_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0204
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0204
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0204_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0205
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0205
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0205_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0206
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0206
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0206_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0207
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0207
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0207_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0208
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0208
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0208_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0209
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0209
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0209_encode
