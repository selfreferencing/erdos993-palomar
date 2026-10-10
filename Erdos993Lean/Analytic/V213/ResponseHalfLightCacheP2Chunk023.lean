module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Chunk022

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 230: mul.
def e0230 : Expr := Expr.mul e0229 e0004
def p0230 : Bi := exact_poly_nf_compact% (mul p0229 p0004)
theorem p0230_op : p0230 = mul p0229 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0230_encode : p0230 = Expr.encode e0230 [[0,1]] [[],[1]] := by
  rw [p0230_op]
  exact congrArg₂ mul p0229_encode p0004_encode

-- Source node 231: mul.
def e0231 : Expr := Expr.mul e0086 e0001
def p0231 : Bi := exact_poly_nf_compact% (mul p0086 p0001)
theorem p0231_op : p0231 = mul p0086 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0231_encode : p0231 = Expr.encode e0231 [[0,1]] [[],[1]] := by
  rw [p0231_op]
  exact congrArg₂ mul p0086_encode p0001_encode

-- Source node 232: add.
def e0232 : Expr := Expr.add e0083 e0231
def p0232 : Bi := exact_poly_nf_compact% (Bi.add p0083 p0231)
theorem p0232_op : p0232 = Bi.add p0083 p0231 := by decide +kernel
theorem p0232_encode : p0232 = Expr.encode e0232 [[0,1]] [[],[1]] := by
  rw [p0232_op]
  exact congrArg₂ Bi.add p0083_encode p0231_encode

-- Source node 233: mul.
def e0233 : Expr := Expr.mul e0230 e0232
def p0233 : Bi := exact_poly_nf_compact% (mul p0230 p0232)
theorem p0233_op : p0233 = mul p0230 p0232 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0233_encode : p0233 = Expr.encode e0233 [[0,1]] [[],[1]] := by
  rw [p0233_op]
  exact congrArg₂ mul p0230_encode p0232_encode

-- Source node 234: add.
def e0234 : Expr := Expr.add e0228 e0233
def p0234 : Bi := exact_poly_nf_compact% (Bi.add p0228 p0233)
theorem p0234_op : p0234 = Bi.add p0228 p0233 := by decide +kernel
theorem p0234_encode : p0234 = Expr.encode e0234 [[0,1]] [[],[1]] := by
  rw [p0234_op]
  exact congrArg₂ Bi.add p0228_encode p0233_encode

theorem source_mixedKNum_027 : e0234 = mixedKNum (⟨1, by decide⟩ : Fin 4) 1 := by rfl

-- Source node 235: mul.
def e0235 : Expr := Expr.mul e0225 e0234
def p0235 : Bi := exact_poly_nf_compact% (mul p0225 p0234)
theorem p0235_op : p0235 = mul p0225 p0234 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0235_encode : p0235 = Expr.encode e0235 [[0,1]] [[],[1]] := by
  rw [p0235_op]
  exact congrArg₂ mul p0225_encode p0234_encode

-- Source node 236: neg.
def e0236 : Expr := Expr.neg e0235
def p0236 : Bi := exact_poly_nf_compact% (neg p0235)
theorem p0236_op : p0236 = neg p0235 := by decide +kernel
theorem p0236_encode : p0236 = Expr.encode e0236 [[0,1]] [[],[1]] := by
  rw [p0236_op]
  exact congrArg neg p0235_encode

-- Source node 237: add.
def e0237 : Expr := Expr.add e0216 e0236
def p0237 : Bi := exact_poly_nf_compact% (Bi.add p0216 p0236)
theorem p0237_op : p0237 = Bi.add p0216 p0236 := by decide +kernel
theorem p0237_encode : p0237 = Expr.encode e0237 [[0,1]] [[],[1]] := by
  rw [p0237_op]
  exact congrArg₂ Bi.add p0216_encode p0236_encode

-- Source node 238: mul.
def e0238 : Expr := Expr.mul e0013 e0050
def p0238 : Bi := exact_poly_nf_compact% (mul p0013 p0050)
theorem p0238_op : p0238 = mul p0013 p0050 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0238_encode : p0238 = Expr.encode e0238 [[0,1]] [[],[1]] := by
  rw [p0238_op]
  exact congrArg₂ mul p0013_encode p0050_encode

-- Source node 239: mul.
def e0239 : Expr := Expr.mul e0238 e0001
def p0239 : Bi := exact_poly_nf_compact% (mul p0238 p0001)
theorem p0239_op : p0239 = mul p0238 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0239_encode : p0239 = Expr.encode e0239 [[0,1]] [[],[1]] := by
  rw [p0239_op]
  exact congrArg₂ mul p0238_encode p0001_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0230
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0230
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0230_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0231
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0231
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0231_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0232
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0232
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0232_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0233
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0233
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0233_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0234
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0234
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0234_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_mixedKNum_027
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_mixedKNum_027
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0235
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0235
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0235_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0236
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0236
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0236_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0237
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0237
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0237_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0238
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0238
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0238_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0239
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0239
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0239_encode
