module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP0Chunk007

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 80: mul.
def e0080 : Expr := Expr.mul e0045 e0001
def p0080 : Bi := exact_poly_nf_compact% (mul p0045 p0001)
theorem p0080_op : p0080 = mul p0045 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0080_encode : p0080 = Expr.encode e0080 [[0,1]] [[],[1]] := by
  rw [p0080_op]
  exact congrArg₂ mul p0045_encode p0001_encode

-- Source node 81: mul.
def e0081 : Expr := Expr.mul e0077 e0028
def p0081 : Bi := exact_poly_nf_compact% (mul p0077 p0028)
theorem p0081_op : p0081 = mul p0077 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0081_encode : p0081 = Expr.encode e0081 [[0,1]] [[],[1]] := by
  rw [p0081_op]
  exact congrArg₂ mul p0077_encode p0028_encode

-- Source node 82: neg.
def e0082 : Expr := Expr.neg e0081
def p0082 : Bi := exact_poly_nf_compact% (neg p0081)
theorem p0082_op : p0082 = neg p0081 := by decide +kernel
theorem p0082_encode : p0082 = Expr.encode e0082 [[0,1]] [[],[1]] := by
  rw [p0082_op]
  exact congrArg neg p0081_encode

-- Source node 83: add.
def e0083 : Expr := Expr.add e0080 e0082
def p0083 : Bi := exact_poly_nf_compact% (Bi.add p0080 p0082)
theorem p0083_op : p0083 = Bi.add p0080 p0082 := by decide +kernel
theorem p0083_encode : p0083 = Expr.encode e0083 [[0,1]] [[],[1]] := by
  rw [p0083_op]
  exact congrArg₂ Bi.add p0080_encode p0082_encode

theorem source_baseANum_019 : e0083 = baseANum (⟨0, by decide⟩ : Fin 4) 1 := by rfl

-- Source node 84: neg.
def e0084 : Expr := Expr.neg e0045
def p0084 : Bi := exact_poly_nf_compact% (neg p0045)
theorem p0084_op : p0084 = neg p0045 := by decide +kernel
theorem p0084_encode : p0084 = Expr.encode e0084 [[0,1]] [[],[1]] := by
  rw [p0084_op]
  exact congrArg neg p0045_encode

-- Source node 85: neg.
def e0085 : Expr := Expr.neg e0066
def p0085 : Bi := exact_poly_nf_compact% (neg p0066)
theorem p0085_op : p0085 = neg p0066 := by decide +kernel
theorem p0085_encode : p0085 = Expr.encode e0085 [[0,1]] [[],[1]] := by
  rw [p0085_op]
  exact congrArg neg p0066_encode

-- Source node 86: add.
def e0086 : Expr := Expr.add e0084 e0085
def p0086 : Bi := exact_poly_nf_compact% (Bi.add p0084 p0085)
theorem p0086_op : p0086 = Bi.add p0084 p0085 := by decide +kernel
theorem p0086_encode : p0086 = Expr.encode e0086 [[0,1]] [[],[1]] := by
  rw [p0086_op]
  exact congrArg₂ Bi.add p0084_encode p0085_encode

theorem source_baseB_020 : e0086 = baseB (⟨0, by decide⟩ : Fin 4) := by rfl

-- Source node 87: constant.
def e0087 : Expr := Expr.constant (((((rowData (⟨0, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0087 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨0, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0087_op : p0087 = ([[(((((rowData (⟨0, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0087_encode : p0087 = Expr.encode e0087 [[0,1]] [[],[1]] := by
  rw [p0087_op]
  rfl

-- Source node 88: constant.
def e0088 : Expr := Expr.constant ((((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)
def p0088 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0088_op : p0088 = ([[((((rowData (⟨0, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0088_encode : p0088 = Expr.encode e0088 [[0,1]] [[],[1]] := by
  rw [p0088_op]
  rfl

-- Source node 89: mul.
def e0089 : Expr := Expr.mul e0088 e0000
def p0089 : Bi := exact_poly_nf_compact% (mul p0088 p0000)
theorem p0089_op : p0089 = mul p0088 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0089_encode : p0089 = Expr.encode e0089 [[0,1]] [[],[1]] := by
  rw [p0089_op]
  exact congrArg₂ mul p0088_encode p0000_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0080
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0080
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0080_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0081
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0081
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0081_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0082
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0082
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0082_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0083
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0083
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0083_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.source_baseANum_019
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.source_baseANum_019
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0084
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0084
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0084_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0085
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0085
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0085_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0086
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0086
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0086_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.source_baseB_020
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.source_baseB_020
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0087
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0087
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0087_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0088
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0088
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0088_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0089
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0089
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0089_encode
