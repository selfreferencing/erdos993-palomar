module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP5Chunk025

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 260: mul.
def e0260 : Expr := Expr.mul e0247 e0259
def p0260 : Bi := exact_poly_nf_compact% (mul p0247 p0259)
theorem p0260_op : p0260 = mul p0247 p0259 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0260_encode : p0260 = Expr.encode e0260 [[0,1]] [[],[1]] := by
  rw [p0260_op]
  exact congrArg₂ mul p0247_encode p0259_encode

-- Source node 261: add.
def e0261 : Expr := Expr.add e0242 e0260
def p0261 : Bi := exact_poly_nf_compact% (Bi.add p0242 p0260)
theorem p0261_op : p0261 = Bi.add p0242 p0260 := by decide +kernel
theorem p0261_encode : p0261 = Expr.encode e0261 [[0,1]] [[],[1]] := by
  rw [p0261_op]
  exact congrArg₂ Bi.add p0242_encode p0260_encode

-- Source node 262: constant.
def e0262 : Expr := Expr.constant ((1/4) : ℚ)
def p0262 : Bi := exact_poly_nf_compact% (([[((1/4) : ℚ)]] : Bi))
theorem p0262_op : p0262 = ([[((1/4) : ℚ)]] : Bi) := by decide +kernel
theorem p0262_encode : p0262 = Expr.encode e0262 [[0,1]] [[],[1]] := by
  rw [p0262_op]
  rfl

-- Source node 263: mul.
def e0263 : Expr := Expr.mul e0262 e0002
def p0263 : Bi := exact_poly_nf_compact% (mul p0262 p0002)
theorem p0263_op : p0263 = mul p0262 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0263_encode : p0263 = Expr.encode e0263 [[0,1]] [[],[1]] := by
  rw [p0263_op]
  exact congrArg₂ mul p0262_encode p0002_encode

-- Source node 264: mul.
def e0264 : Expr := Expr.mul e0263 e0012
def p0264 : Bi := exact_poly_nf_compact% (mul p0263 p0012)
theorem p0264_op : p0264 = mul p0263 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0264_encode : p0264 = Expr.encode e0264 [[0,1]] [[],[1]] := by
  rw [p0264_op]
  exact congrArg₂ mul p0263_encode p0012_encode

-- Source node 265: mul.
def e0265 : Expr := Expr.mul e0264 e0166
def p0265 : Bi := exact_poly_nf_compact% (mul p0264 p0166)
theorem p0265_op : p0265 = mul p0264 p0166 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0265_encode : p0265 = Expr.encode e0265 [[0,1]] [[],[1]] := by
  rw [p0265_op]
  exact congrArg₂ mul p0264_encode p0166_encode

-- Source node 266: mul.
def e0266 : Expr := Expr.mul e0265 e0001
def p0266 : Bi := exact_poly_nf_compact% (mul p0265 p0001)
theorem p0266_op : p0266 = mul p0265 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0266_encode : p0266 = Expr.encode e0266 [[0,1]] [[],[1]] := by
  rw [p0266_op]
  exact congrArg₂ mul p0265_encode p0001_encode

-- Source node 267: mul.
def e0267 : Expr := Expr.mul e0266 e0099
def p0267 : Bi := exact_poly_nf_compact% (mul p0266 p0099)
theorem p0267_op : p0267 = mul p0266 p0099 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0267_encode : p0267 = Expr.encode e0267 [[0,1]] [[],[1]] := by
  rw [p0267_op]
  exact congrArg₂ mul p0266_encode p0099_encode

-- Source node 268: pow_zero.
def e0268 : Expr := Expr.pow e0134 0
def p0268 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0268_op : p0268 = ([[1]] : Bi) := by decide +kernel
theorem p0268_encode : p0268 = Expr.encode e0268 [[0,1]] [[],[1]] := by
  rw [p0268_op]
  rfl

-- Source node 269: pow_succ.
def e0269 : Expr := Expr.pow e0134 1
def p0269 : Bi := exact_poly_nf_compact% (mul p0268 p0134)
theorem p0269_op : p0269 = mul p0268 p0134 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0269_encode : p0269 = Expr.encode e0269 [[0,1]] [[],[1]] := by
  rw [p0269_op]
  exact congrArg₂ mul p0268_encode p0134_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0260
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0260
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0260_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0261
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0261
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0261_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0262
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0262
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0262_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0263
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0263
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0263_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0264
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0264
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0264_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0265
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0265
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0265_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0266
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0266
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0266_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0267
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0267
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0267_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0268
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0268
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0268_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0269
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0269
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0269_encode
