module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Chunk023

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 240: add.
def e0240 : Expr := Expr.add e0219 e0239
def p0240 : Bi := exact_poly_nf_compact% (Bi.add p0219 p0239)
theorem p0240_op : p0240 = Bi.add p0219 p0239 := by decide +kernel
theorem p0240_encode : p0240 = Expr.encode e0240 [[0,1]] [[],[1]] := by
  rw [p0240_op]
  exact congrArg₂ Bi.add p0219_encode p0239_encode

-- Source node 241: mul.
def e0241 : Expr := Expr.mul e0013 e0051
def p0241 : Bi := exact_poly_nf_compact% (mul p0013 p0051)
theorem p0241_op : p0241 = mul p0013 p0051 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0241_encode : p0241 = Expr.encode e0241 [[0,1]] [[],[1]] := by
  rw [p0241_op]
  exact congrArg₂ mul p0013_encode p0051_encode

-- Source node 242: mul.
def e0242 : Expr := Expr.mul e0241 e0001
def p0242 : Bi := exact_poly_nf_compact% (mul p0241 p0001)
theorem p0242_op : p0242 = mul p0241 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0242_encode : p0242 = Expr.encode e0242 [[0,1]] [[],[1]] := by
  rw [p0242_op]
  exact congrArg₂ mul p0241_encode p0001_encode

-- Source node 243: mul.
def e0243 : Expr := Expr.mul e0242 e0164
def p0243 : Bi := exact_poly_nf_compact% (mul p0242 p0164)
theorem p0243_op : p0243 = mul p0242 p0164 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0243_encode : p0243 = Expr.encode e0243 [[0,1]] [[],[1]] := by
  rw [p0243_op]
  exact congrArg₂ mul p0242_encode p0164_encode

-- Source node 244: mul.
def e0244 : Expr := Expr.mul e0243 e0097
def p0244 : Bi := exact_poly_nf_compact% (mul p0243 p0097)
theorem p0244_op : p0244 = mul p0243 p0097 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0244_encode : p0244 = Expr.encode e0244 [[0,1]] [[],[1]] := by
  rw [p0244_op]
  exact congrArg₂ mul p0243_encode p0097_encode

-- Source node 245: mul.
def e0245 : Expr := Expr.mul e0244 e0039
def p0245 : Bi := exact_poly_nf_compact% (mul p0244 p0039)
theorem p0245_op : p0245 = mul p0244 p0039 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0245_encode : p0245 = Expr.encode e0245 [[0,1]] [[],[1]] := by
  rw [p0245_op]
  exact congrArg₂ mul p0244_encode p0039_encode

-- Source node 246: mul.
def e0246 : Expr := Expr.mul e0229 e0012
def p0246 : Bi := exact_poly_nf_compact% (mul p0229 p0012)
theorem p0246_op : p0246 = mul p0229 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0246_encode : p0246 = Expr.encode e0246 [[0,1]] [[],[1]] := by
  rw [p0246_op]
  exact congrArg₂ mul p0229_encode p0012_encode

-- Source node 247: mul.
def e0247 : Expr := Expr.mul e0246 e0028
def p0247 : Bi := exact_poly_nf_compact% (mul p0246 p0028)
theorem p0247_op : p0247 = mul p0246 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0247_encode : p0247 = Expr.encode e0247 [[0,1]] [[],[1]] := by
  rw [p0247_op]
  exact congrArg₂ mul p0246_encode p0028_encode

-- Source node 248: mul.
def e0248 : Expr := Expr.mul e0247 e0086
def p0248 : Bi := exact_poly_nf_compact% (mul p0247 p0086)
theorem p0248_op : p0248 = mul p0247 p0086 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0248_encode : p0248 = Expr.encode e0248 [[0,1]] [[],[1]] := by
  rw [p0248_op]
  exact congrArg₂ mul p0247_encode p0086_encode

-- Source node 249: mul.
def e0249 : Expr := Expr.mul e0031 e0004
def p0249 : Bi := exact_poly_nf_compact% (mul p0031 p0004)
theorem p0249_op : p0249 = mul p0031 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0249_encode : p0249 = Expr.encode e0249 [[0,1]] [[],[1]] := by
  rw [p0249_op]
  exact congrArg₂ mul p0031_encode p0004_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0240
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0240
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0240_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0241
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0241
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0241_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0242
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0242
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0242_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0243
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0243
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0243_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0244
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0244
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0244_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0245
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0245
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0245_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0246
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0246
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0246_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0247
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0247
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0247_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0248
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0248
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0248_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0249
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0249
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0249_encode
