module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP4Chunk024

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 250: mul.
def e0250 : Expr := Expr.mul e0249 e0012
def p0250 : Bi := exact_poly_nf_compact% (mul p0249 p0012)
theorem p0250_op : p0250 = mul p0249 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0250_encode : p0250 = Expr.encode e0250 [[0,1]] [[],[1]] := by
  rw [p0250_op]
  exact congrArg₂ mul p0249_encode p0012_encode

-- Source node 251: mul.
def e0251 : Expr := Expr.mul e0250 e0028
def p0251 : Bi := exact_poly_nf_compact% (mul p0250 p0028)
theorem p0251_op : p0251 = mul p0250 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0251_encode : p0251 = Expr.encode e0251 [[0,1]] [[],[1]] := by
  rw [p0251_op]
  exact congrArg₂ mul p0250_encode p0028_encode

-- Source node 252: mul.
def e0252 : Expr := Expr.mul e0251 e0004
def p0252 : Bi := exact_poly_nf_compact% (mul p0251 p0004)
theorem p0252_op : p0252 = mul p0251 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0252_encode : p0252 = Expr.encode e0252 [[0,1]] [[],[1]] := by
  rw [p0252_op]
  exact congrArg₂ mul p0251_encode p0004_encode

-- Source node 253: mul.
def e0253 : Expr := Expr.mul e0252 e0086
def p0253 : Bi := exact_poly_nf_compact% (mul p0252 p0086)
theorem p0253_op : p0253 = mul p0252 p0086 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0253_encode : p0253 = Expr.encode e0253 [[0,1]] [[],[1]] := by
  rw [p0253_op]
  exact congrArg₂ mul p0252_encode p0086_encode

-- Source node 254: add.
def e0254 : Expr := Expr.add e0248 e0253
def p0254 : Bi := exact_poly_nf_compact% (Bi.add p0248 p0253)
theorem p0254_op : p0254 = Bi.add p0248 p0253 := by decide +kernel
theorem p0254_encode : p0254 = Expr.encode e0254 [[0,1]] [[],[1]] := by
  rw [p0254_op]
  exact congrArg₂ Bi.add p0248_encode p0253_encode

theorem source_mixedANum_028 : e0254 = mixedANum (⟨2, by decide⟩ : Fin 4) 1 := by rfl

-- Source node 255: mul.
def e0255 : Expr := Expr.mul e0242 e0254
def p0255 : Bi := exact_poly_nf_compact% (mul p0242 p0254)
theorem p0255_op : p0255 = mul p0242 p0254 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0255_encode : p0255 = Expr.encode e0255 [[0,1]] [[],[1]] := by
  rw [p0255_op]
  exact congrArg₂ mul p0242_encode p0254_encode

-- Source node 256: add.
def e0256 : Expr := Expr.add e0237 e0255
def p0256 : Bi := exact_poly_nf_compact% (Bi.add p0237 p0255)
theorem p0256_op : p0256 = Bi.add p0237 p0255 := by decide +kernel
theorem p0256_encode : p0256 = Expr.encode e0256 [[0,1]] [[],[1]] := by
  rw [p0256_op]
  exact congrArg₂ Bi.add p0237_encode p0255_encode

-- Source node 257: constant.
def e0257 : Expr := Expr.constant ((1/4) : ℚ)
def p0257 : Bi := exact_poly_nf_compact% (([[((1/4) : ℚ)]] : Bi))
theorem p0257_op : p0257 = ([[((1/4) : ℚ)]] : Bi) := by decide +kernel
theorem p0257_encode : p0257 = Expr.encode e0257 [[0,1]] [[],[1]] := by
  rw [p0257_op]
  rfl

-- Source node 258: mul.
def e0258 : Expr := Expr.mul e0257 e0002
def p0258 : Bi := exact_poly_nf_compact% (mul p0257 p0002)
theorem p0258_op : p0258 = mul p0257 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0258_encode : p0258 = Expr.encode e0258 [[0,1]] [[],[1]] := by
  rw [p0258_op]
  exact congrArg₂ mul p0257_encode p0002_encode

-- Source node 259: mul.
def e0259 : Expr := Expr.mul e0258 e0012
def p0259 : Bi := exact_poly_nf_compact% (mul p0258 p0012)
theorem p0259_op : p0259 = mul p0258 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0259_encode : p0259 = Expr.encode e0259 [[0,1]] [[],[1]] := by
  rw [p0259_op]
  exact congrArg₂ mul p0258_encode p0012_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0250
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0250
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0250_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0251
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0251
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0251_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0252
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0252
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0252_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0253
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0253
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0253_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0254
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0254
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0254_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_mixedANum_028
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_mixedANum_028
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0255
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0255
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0255_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0256
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0256
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0256_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0257
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0257
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0257_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0258
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0258
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0258_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0259
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0259
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0259_encode
