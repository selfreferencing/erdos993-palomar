module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP4Chunk027

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 280: mul.
def e0280 : Expr := Expr.mul e0279 e0116
def p0280 : Bi := exact_poly_nf_compact% (mul p0279 p0116)
theorem p0280_op : p0280 = mul p0279 p0116 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0280_encode : p0280 = Expr.encode e0280 [[0,1]] [[],[1]] := by
  rw [p0280_op]
  exact congrArg₂ mul p0279_encode p0116_encode

-- Source node 281: neg.
def e0281 : Expr := Expr.neg e0280
def p0281 : Bi := exact_poly_nf_compact% (neg p0280)
theorem p0281_op : p0281 = neg p0280 := by decide +kernel
theorem p0281_encode : p0281 = Expr.encode e0281 [[0,1]] [[],[1]] := by
  rw [p0281_op]
  exact congrArg neg p0280_encode

-- Source node 282: add.
def e0282 : Expr := Expr.add e0268 e0281
def p0282 : Bi := exact_poly_nf_compact% (Bi.add p0268 p0281)
theorem p0282_op : p0282 = Bi.add p0268 p0281 := by decide +kernel
theorem p0282_encode : p0282 = Expr.encode e0282 [[0,1]] [[],[1]] := by
  rw [p0282_op]
  exact congrArg₂ Bi.add p0268_encode p0281_encode

theorem source_unweightedDeterminantPoly_029 : e0282 = unweightedDeterminantPoly (⟨2, by decide⟩ : Fin 4) 1 := by rfl

-- Source node 283: constant.
def e0283 : Expr := Expr.constant ((omegaQ (⟨4, by decide⟩ : Fin 8)) : ℚ)
def p0283 : Bi := exact_poly_nf_compact% (([[((omegaQ (⟨4, by decide⟩ : Fin 8)) : ℚ)]] : Bi))
theorem p0283_op : p0283 = ([[((omegaQ (⟨4, by decide⟩ : Fin 8)) : ℚ)]] : Bi) := by decide +kernel
theorem p0283_encode : p0283 = Expr.encode e0283 [[0,1]] [[],[1]] := by
  rw [p0283_op]
  rfl

-- Source node 284: mul.
def e0284 : Expr := Expr.mul e0283 e0282
def p0284 : Bi := exact_poly_nf_compact% (mul p0283 p0282)
theorem p0284_op : p0284 = mul p0283 p0282 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0284_encode : p0284 = Expr.encode e0284 [[0,1]] [[],[1]] := by
  rw [p0284_op]
  exact congrArg₂ mul p0283_encode p0282_encode

theorem source_determinantExpression : e0284 = determinantExpression (⟨4, by decide⟩ : Fin 8) := by rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0280
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0280
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0280_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0281
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0281
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0281_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0282
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0282
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0282_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_unweightedDeterminantPoly_029
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_unweightedDeterminantPoly_029
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0283
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0283
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0283_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0284
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0284
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0284_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_determinantExpression
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_determinantExpression
