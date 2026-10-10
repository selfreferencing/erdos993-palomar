module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP3Chunk027

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 280: mul.
def e0280 : Expr := Expr.mul e0279 e0001
def p0280 : Bi := exact_poly_nf_compact% (mul p0279 p0001)
theorem p0280_op : p0280 = mul p0279 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0280_encode : p0280 = Expr.encode e0280 [[0,1]] [[],[1]] := by
  rw [p0280_op]
  exact congrArg₂ mul p0279_encode p0001_encode

-- Source node 281: mul.
def e0281 : Expr := Expr.mul e0280 e0042
def p0281 : Bi := exact_poly_nf_compact% (mul p0280 p0042)
theorem p0281_op : p0281 = mul p0280 p0042 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0281_encode : p0281 = Expr.encode e0281 [[0,1]] [[],[1]] := by
  rw [p0281_op]
  exact congrArg₂ mul p0280_encode p0042_encode

-- Source node 282: mul.
def e0282 : Expr := Expr.mul e0281 e0095
def p0282 : Bi := exact_poly_nf_compact% (mul p0281 p0095)
theorem p0282_op : p0282 = mul p0281 p0095 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0282_encode : p0282 = Expr.encode e0282 [[0,1]] [[],[1]] := by
  rw [p0282_op]
  exact congrArg₂ mul p0281_encode p0095_encode

-- Source node 283: mul.
def e0283 : Expr := Expr.mul e0282 e0099
def p0283 : Bi := exact_poly_nf_compact% (mul p0282 p0099)
theorem p0283_op : p0283 = mul p0282 p0099 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0283_encode : p0283 = Expr.encode e0283 [[0,1]] [[],[1]] := by
  rw [p0283_op]
  exact congrArg₂ mul p0282_encode p0099_encode

-- Source node 284: mul.
def e0284 : Expr := Expr.mul e0283 e0124
def p0284 : Bi := exact_poly_nf_compact% (mul p0283 p0124)
theorem p0284_op : p0284 = mul p0283 p0124 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0284_encode : p0284 = Expr.encode e0284 [[0,1]] [[],[1]] := by
  rw [p0284_op]
  exact congrArg₂ mul p0283_encode p0124_encode

-- Source node 285: mul.
def e0285 : Expr := Expr.mul e0284 e0121
def p0285 : Bi := exact_poly_nf_compact% (mul p0284 p0121)
theorem p0285_op : p0285 = mul p0284 p0121 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0285_encode : p0285 = Expr.encode e0285 [[0,1]] [[],[1]] := by
  rw [p0285_op]
  exact congrArg₂ mul p0284_encode p0121_encode

-- Source node 286: neg.
def e0286 : Expr := Expr.neg e0285
def p0286 : Bi := exact_poly_nf_compact% (neg p0285)
theorem p0286_op : p0286 = neg p0285 := by decide +kernel
theorem p0286_encode : p0286 = Expr.encode e0286 [[0,1]] [[],[1]] := by
  rw [p0286_op]
  exact congrArg neg p0285_encode

-- Source node 287: add.
def e0287 : Expr := Expr.add e0273 e0286
def p0287 : Bi := exact_poly_nf_compact% (Bi.add p0273 p0286)
theorem p0287_op : p0287 = Bi.add p0273 p0286 := by decide +kernel
theorem p0287_encode : p0287 = Expr.encode e0287 [[0,1]] [[],[1]] := by
  rw [p0287_op]
  exact congrArg₂ Bi.add p0273_encode p0286_encode

theorem source_unweightedDeterminantPoly_029 : e0287 = unweightedDeterminantPoly (⟨1, by decide⟩ : Fin 4) 2 := by rfl

-- Source node 288: constant.
def e0288 : Expr := Expr.constant ((omegaQ (⟨3, by decide⟩ : Fin 8)) : ℚ)
def p0288 : Bi := exact_poly_nf_compact% (([[((omegaQ (⟨3, by decide⟩ : Fin 8)) : ℚ)]] : Bi))
theorem p0288_op : p0288 = ([[((omegaQ (⟨3, by decide⟩ : Fin 8)) : ℚ)]] : Bi) := by decide +kernel
theorem p0288_encode : p0288 = Expr.encode e0288 [[0,1]] [[],[1]] := by
  rw [p0288_op]
  rfl

-- Source node 289: mul.
def e0289 : Expr := Expr.mul e0288 e0287
def p0289 : Bi := exact_poly_nf_compact% (mul p0288 p0287)
theorem p0289_op : p0289 = mul p0288 p0287 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0289_encode : p0289 = Expr.encode e0289 [[0,1]] [[],[1]] := by
  rw [p0289_op]
  exact congrArg₂ mul p0288_encode p0287_encode

theorem source_determinantExpression : e0289 = determinantExpression (⟨3, by decide⟩ : Fin 8) := by rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0280
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0280
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0280_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0281
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0281
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0281_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0282
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0282
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0282_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0283
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0283
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0283_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0284
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0284
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0284_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0285
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0285
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0285_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0286
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0286
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0286_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0287
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0287
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0287_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.source_unweightedDeterminantPoly_029
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.source_unweightedDeterminantPoly_029
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0288
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0288
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0288_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0289
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0289
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0289_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.source_determinantExpression
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.source_determinantExpression
