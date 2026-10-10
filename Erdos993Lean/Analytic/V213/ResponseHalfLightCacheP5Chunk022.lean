module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP5Chunk021

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 220: mul.
def e0220 : Expr := Expr.mul e0216 e0219
def p0220 : Bi := exact_poly_nf_compact% (mul p0216 p0219)
theorem p0220_op : p0220 = mul p0216 p0219 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0220_encode : p0220 = Expr.encode e0220 [[0,1]] [[],[1]] := by
  rw [p0220_op]
  exact congrArg₂ mul p0216_encode p0219_encode

-- Source node 221: add.
def e0221 : Expr := Expr.add e0207 e0220
def p0221 : Bi := exact_poly_nf_compact% (Bi.add p0207 p0220)
theorem p0221_op : p0221 = Bi.add p0207 p0220 := by decide +kernel
theorem p0221_encode : p0221 = Expr.encode e0221 [[0,1]] [[],[1]] := by
  rw [p0221_op]
  exact congrArg₂ Bi.add p0207_encode p0220_encode

-- Source node 222: constant.
def e0222 : Expr := Expr.constant ((1/20) : ℚ)
def p0222 : Bi := exact_poly_nf_compact% (([[((1/20) : ℚ)]] : Bi))
theorem p0222_op : p0222 = ([[((1/20) : ℚ)]] : Bi) := by decide +kernel
theorem p0222_encode : p0222 = Expr.encode e0222 [[0,1]] [[],[1]] := by
  rw [p0222_op]
  rfl

-- Source node 223: mul.
def e0223 : Expr := Expr.mul e0222 e0023
def p0223 : Bi := exact_poly_nf_compact% (mul p0222 p0023)
theorem p0223_op : p0223 = mul p0222 p0023 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0223_encode : p0223 = Expr.encode e0223 [[0,1]] [[],[1]] := by
  rw [p0223_op]
  exact congrArg₂ mul p0222_encode p0023_encode

-- Source node 224: mul.
def e0224 : Expr := Expr.mul e0223 e0035
def p0224 : Bi := exact_poly_nf_compact% (mul p0223 p0035)
theorem p0224_op : p0224 = mul p0223 p0035 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0224_encode : p0224 = Expr.encode e0224 [[0,1]] [[],[1]] := by
  rw [p0224_op]
  exact congrArg₂ mul p0223_encode p0035_encode

-- Source node 225: mul.
def e0225 : Expr := Expr.mul e0224 e0006
def p0225 : Bi := exact_poly_nf_compact% (mul p0224 p0006)
theorem p0225_op : p0225 = mul p0224 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0225_encode : p0225 = Expr.encode e0225 [[0,1]] [[],[1]] := by
  rw [p0225_op]
  exact congrArg₂ mul p0224_encode p0006_encode

-- Source node 226: mul.
def e0226 : Expr := Expr.mul e0225 e0006
def p0226 : Bi := exact_poly_nf_compact% (mul p0225 p0006)
theorem p0226_op : p0226 = mul p0225 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0226_encode : p0226 = Expr.encode e0226 [[0,1]] [[],[1]] := by
  rw [p0226_op]
  exact congrArg₂ mul p0225_encode p0006_encode

-- Source node 227: mul.
def e0227 : Expr := Expr.mul e0226 e0019
def p0227 : Bi := exact_poly_nf_compact% (mul p0226 p0019)
theorem p0227_op : p0227 = mul p0226 p0019 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0227_encode : p0227 = Expr.encode e0227 [[0,1]] [[],[1]] := by
  rw [p0227_op]
  exact congrArg₂ mul p0226_encode p0019_encode

-- Source node 228: mul.
def e0228 : Expr := Expr.mul e0227 e0095
def p0228 : Bi := exact_poly_nf_compact% (mul p0227 p0095)
theorem p0228_op : p0228 = mul p0227 p0095 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0228_encode : p0228 = Expr.encode e0228 [[0,1]] [[],[1]] := by
  rw [p0228_op]
  exact congrArg₂ mul p0227_encode p0095_encode

-- Source node 229: mul.
def e0229 : Expr := Expr.mul e0228 e0124
def p0229 : Bi := exact_poly_nf_compact% (mul p0228 p0124)
theorem p0229_op : p0229 = mul p0228 p0124 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0229_encode : p0229 = Expr.encode e0229 [[0,1]] [[],[1]] := by
  rw [p0229_op]
  exact congrArg₂ mul p0228_encode p0124_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0220
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0220
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0220_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0221
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0221
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0221_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0222
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0222
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0222_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0223
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0223
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0223_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0224
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0224
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0224_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0225
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0225
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0225_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0226
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0226
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0226_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0227
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0227
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0227_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0228
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0228
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0228_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0229
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0229
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0229_encode
