module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Chunk026

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 270: neg.
def e0270 : Expr := Expr.neg e0269
def p0270 : Bi := exact_poly_nf_compact% (neg p0269)
theorem p0270_op : p0270 = neg p0269 := by decide +kernel
theorem p0270_encode : p0270 = Expr.encode e0270 [[0,1]] [[],[1]] := by
  rw [p0270_op]
  exact congrArg neg p0269_encode

-- Source node 271: add.
def e0271 : Expr := Expr.add e0259 e0270
def p0271 : Bi := exact_poly_nf_compact% (Bi.add p0259 p0270)
theorem p0271_op : p0271 = Bi.add p0259 p0270 := by decide +kernel
theorem p0271_encode : p0271 = Expr.encode e0271 [[0,1]] [[],[1]] := by
  rw [p0271_op]
  exact congrArg₂ Bi.add p0259_encode p0270_encode

-- Source node 272: constant.
def e0272 : Expr := Expr.constant ((1/10) : ℚ)
def p0272 : Bi := exact_poly_nf_compact% (([[((1/10) : ℚ)]] : Bi))
theorem p0272_op : p0272 = ([[((1/10) : ℚ)]] : Bi) := by decide +kernel
theorem p0272_encode : p0272 = Expr.encode e0272 [[0,1]] [[],[1]] := by
  rw [p0272_op]
  rfl

-- Source node 273: mul.
def e0273 : Expr := Expr.mul e0272 e0000
def p0273 : Bi := exact_poly_nf_compact% (mul p0272 p0000)
theorem p0273_op : p0273 = mul p0272 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0273_encode : p0273 = Expr.encode e0273 [[0,1]] [[],[1]] := by
  rw [p0273_op]
  exact congrArg₂ mul p0272_encode p0000_encode

-- Source node 274: mul.
def e0274 : Expr := Expr.mul e0273 e0002
def p0274 : Bi := exact_poly_nf_compact% (mul p0273 p0002)
theorem p0274_op : p0274 = mul p0273 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0274_encode : p0274 = Expr.encode e0274 [[0,1]] [[],[1]] := by
  rw [p0274_op]
  exact congrArg₂ mul p0273_encode p0002_encode

-- Source node 275: mul.
def e0275 : Expr := Expr.mul e0274 e0001
def p0275 : Bi := exact_poly_nf_compact% (mul p0274 p0001)
theorem p0275_op : p0275 = mul p0274 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0275_encode : p0275 = Expr.encode e0275 [[0,1]] [[],[1]] := by
  rw [p0275_op]
  exact congrArg₂ mul p0274_encode p0001_encode

-- Source node 276: mul.
def e0276 : Expr := Expr.mul e0275 e0012
def p0276 : Bi := exact_poly_nf_compact% (mul p0275 p0012)
theorem p0276_op : p0276 = mul p0275 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0276_encode : p0276 = Expr.encode e0276 [[0,1]] [[],[1]] := by
  rw [p0276_op]
  exact congrArg₂ mul p0275_encode p0012_encode

-- Source node 277: mul.
def e0277 : Expr := Expr.mul e0276 e0103
def p0277 : Bi := exact_poly_nf_compact% (mul p0276 p0103)
theorem p0277_op : p0277 = mul p0276 p0103 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0277_encode : p0277 = Expr.encode e0277 [[0,1]] [[],[1]] := by
  rw [p0277_op]
  exact congrArg₂ mul p0276_encode p0103_encode

-- Source node 278: mul.
def e0278 : Expr := Expr.mul e0277 e0031
def p0278 : Bi := exact_poly_nf_compact% (mul p0277 p0031)
theorem p0278_op : p0278 = mul p0277 p0031 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0278_encode : p0278 = Expr.encode e0278 [[0,1]] [[],[1]] := by
  rw [p0278_op]
  exact congrArg₂ mul p0277_encode p0031_encode

-- Source node 279: mul.
def e0279 : Expr := Expr.mul e0278 e0039
def p0279 : Bi := exact_poly_nf_compact% (mul p0278 p0039)
theorem p0279_op : p0279 = mul p0278 p0039 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0279_encode : p0279 = Expr.encode e0279 [[0,1]] [[],[1]] := by
  rw [p0279_op]
  exact congrArg₂ mul p0278_encode p0039_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0270
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0270
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0270_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0271
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0271
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0271_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0272
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0272
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0272_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0273
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0273
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0273_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0274
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0274
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0274_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0275
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0275
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0275_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0276
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0276
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0276_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0277
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0277
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0277_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0278
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0278
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0278_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0279
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0279
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0279_encode
