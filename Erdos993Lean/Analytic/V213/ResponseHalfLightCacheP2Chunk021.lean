module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Chunk020

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 210: mul.
def e0210 : Expr := Expr.mul e0209 e0119
def p0210 : Bi := exact_poly_nf_compact% (mul p0209 p0119)
theorem p0210_op : p0210 = mul p0209 p0119 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0210_encode : p0210 = Expr.encode e0210 [[0,1]] [[],[1]] := by
  rw [p0210_op]
  exact congrArg₂ mul p0209_encode p0119_encode

-- Source node 211: mul.
def e0211 : Expr := Expr.mul e0210 e0004
def p0211 : Bi := exact_poly_nf_compact% (mul p0210 p0004)
theorem p0211_op : p0211 = mul p0210 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0211_encode : p0211 = Expr.encode e0211 [[0,1]] [[],[1]] := by
  rw [p0211_op]
  exact congrArg₂ mul p0210_encode p0004_encode

-- Source node 212: pow_zero.
def e0212 : Expr := Expr.pow e0124 0
def p0212 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0212_op : p0212 = ([[1]] : Bi) := by decide +kernel
theorem p0212_encode : p0212 = Expr.encode e0212 [[0,1]] [[],[1]] := by
  rw [p0212_op]
  rfl

-- Source node 213: pow_succ.
def e0213 : Expr := Expr.pow e0124 1
def p0213 : Bi := exact_poly_nf_compact% (mul p0212 p0124)
theorem p0213_op : p0213 = mul p0212 p0124 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0213_encode : p0213 = Expr.encode e0213 [[0,1]] [[],[1]] := by
  rw [p0213_op]
  exact congrArg₂ mul p0212_encode p0124_encode

-- Source node 214: pow_succ.
def e0214 : Expr := Expr.pow e0124 2
def p0214 : Bi := exact_poly_nf_compact% (mul p0213 p0124)
theorem p0214_op : p0214 = mul p0213 p0124 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0214_encode : p0214 = Expr.encode e0214 [[0,1]] [[],[1]] := by
  rw [p0214_op]
  exact congrArg₂ mul p0213_encode p0124_encode

-- Source node 215: mul.
def e0215 : Expr := Expr.mul e0211 e0214
def p0215 : Bi := exact_poly_nf_compact% (mul p0211 p0214)
theorem p0215_op : p0215 = mul p0211 p0214 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0215_encode : p0215 = Expr.encode e0215 [[0,1]] [[],[1]] := by
  rw [p0215_op]
  exact congrArg₂ mul p0211_encode p0214_encode

-- Source node 216: add.
def e0216 : Expr := Expr.add e0202 e0215
def p0216 : Bi := exact_poly_nf_compact% (Bi.add p0202 p0215)
theorem p0216_op : p0216 = Bi.add p0202 p0215 := by decide +kernel
theorem p0216_encode : p0216 = Expr.encode e0216 [[0,1]] [[],[1]] := by
  rw [p0216_op]
  exact congrArg₂ Bi.add p0202_encode p0215_encode

-- Source node 217: constant.
def e0217 : Expr := Expr.constant ((1/20) : ℚ)
def p0217 : Bi := exact_poly_nf_compact% (([[((1/20) : ℚ)]] : Bi))
theorem p0217_op : p0217 = ([[((1/20) : ℚ)]] : Bi) := by decide +kernel
theorem p0217_encode : p0217 = Expr.encode e0217 [[0,1]] [[],[1]] := by
  rw [p0217_op]
  rfl

-- Source node 218: mul.
def e0218 : Expr := Expr.mul e0217 e0023
def p0218 : Bi := exact_poly_nf_compact% (mul p0217 p0023)
theorem p0218_op : p0218 = mul p0217 p0023 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0218_encode : p0218 = Expr.encode e0218 [[0,1]] [[],[1]] := by
  rw [p0218_op]
  exact congrArg₂ mul p0217_encode p0023_encode

-- Source node 219: mul.
def e0219 : Expr := Expr.mul e0218 e0050
def p0219 : Bi := exact_poly_nf_compact% (mul p0218 p0050)
theorem p0219_op : p0219 = mul p0218 p0050 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0219_encode : p0219 = Expr.encode e0219 [[0,1]] [[],[1]] := by
  rw [p0219_op]
  exact congrArg₂ mul p0218_encode p0050_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0210
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0210
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0210_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0211
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0211
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0211_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0212
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0212
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0212_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0213
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0213
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0213_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0214
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0214
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0214_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0215
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0215
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0215_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0216
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0216
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0216_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0217
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0217
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0217_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0218
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0218
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0218_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0219
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0219
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0219_encode
