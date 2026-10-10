module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP5Chunk008

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 90: neg.
def e0090 : Expr := Expr.neg e0071
def p0090 : Bi := exact_poly_nf_compact% (neg p0071)
theorem p0090_op : p0090 = neg p0071 := by decide +kernel
theorem p0090_encode : p0090 = Expr.encode e0090 [[0,1]] [[],[1]] := by
  rw [p0090_op]
  exact congrArg neg p0071_encode

-- Source node 91: add.
def e0091 : Expr := Expr.add e0089 e0090
def p0091 : Bi := exact_poly_nf_compact% (Bi.add p0089 p0090)
theorem p0091_op : p0091 = Bi.add p0089 p0090 := by decide +kernel
theorem p0091_encode : p0091 = Expr.encode e0091 [[0,1]] [[],[1]] := by
  rw [p0091_op]
  exact congrArg₂ Bi.add p0089_encode p0090_encode

theorem source_baseB_020 : e0091 = baseB (⟨2, by decide⟩ : Fin 4) := by rfl

-- Source node 92: constant.
def e0092 : Expr := Expr.constant (((((rowData (⟨2, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0092 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨2, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0092_op : p0092 = ([[(((((rowData (⟨2, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0092_encode : p0092 = Expr.encode e0092 [[0,1]] [[],[1]] := by
  rw [p0092_op]
  rfl

-- Source node 93: constant.
def e0093 : Expr := Expr.constant ((((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)
def p0093 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0093_op : p0093 = ([[((((rowData (⟨2, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0093_encode : p0093 = Expr.encode e0093 [[0,1]] [[],[1]] := by
  rw [p0093_op]
  rfl

-- Source node 94: mul.
def e0094 : Expr := Expr.mul e0093 e0000
def p0094 : Bi := exact_poly_nf_compact% (mul p0093 p0000)
theorem p0094_op : p0094 = mul p0093 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0094_encode : p0094 = Expr.encode e0094 [[0,1]] [[],[1]] := by
  rw [p0094_op]
  exact congrArg₂ mul p0093_encode p0000_encode

-- Source node 95: add.
def e0095 : Expr := Expr.add e0092 e0094
def p0095 : Bi := exact_poly_nf_compact% (Bi.add p0092 p0094)
theorem p0095_op : p0095 = Bi.add p0092 p0094 := by decide +kernel
theorem p0095_encode : p0095 = Expr.encode e0095 [[0,1]] [[],[1]] := by
  rw [p0095_op]
  exact congrArg₂ Bi.add p0092_encode p0094_encode

theorem source_fieldPolynomial_021 : e0095 = fieldPolynomial (⟨2, by decide⟩ : Fin 4) (rowData (⟨2, by decide⟩ : Fin 4)).gamma0 (rowData (⟨2, by decide⟩ : Fin 4)).gamma1 := by rfl

theorem source_gammaPoly_022 : e0095 = gammaPoly (⟨2, by decide⟩ : Fin 4) := by rfl

-- Source node 96: constant.
def e0096 : Expr := Expr.constant (((((rowData (⟨2, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0096 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨2, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0096_op : p0096 = ([[(((((rowData (⟨2, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨2, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0096_encode : p0096 = Expr.encode e0096 [[0,1]] [[],[1]] := by
  rw [p0096_op]
  rfl

-- Source node 97: constant.
def e0097 : Expr := Expr.constant ((((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)
def p0097 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0097_op : p0097 = ([[((((rowData (⟨2, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0097_encode : p0097 = Expr.encode e0097 [[0,1]] [[],[1]] := by
  rw [p0097_op]
  rfl

-- Source node 98: mul.
def e0098 : Expr := Expr.mul e0097 e0000
def p0098 : Bi := exact_poly_nf_compact% (mul p0097 p0000)
theorem p0098_op : p0098 = mul p0097 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0098_encode : p0098 = Expr.encode e0098 [[0,1]] [[],[1]] := by
  rw [p0098_op]
  exact congrArg₂ mul p0097_encode p0000_encode

-- Source node 99: add.
def e0099 : Expr := Expr.add e0096 e0098
def p0099 : Bi := exact_poly_nf_compact% (Bi.add p0096 p0098)
theorem p0099_op : p0099 = Bi.add p0096 p0098 := by decide +kernel
theorem p0099_encode : p0099 = Expr.encode e0099 [[0,1]] [[],[1]] := by
  rw [p0099_op]
  exact congrArg₂ Bi.add p0096_encode p0098_encode

theorem source_fieldPolynomial_023 : e0099 = fieldPolynomial (⟨2, by decide⟩ : Fin 4) (rowData (⟨2, by decide⟩ : Fin 4)).delta0 (rowData (⟨2, by decide⟩ : Fin 4)).delta1 := by rfl

theorem source_deltaPoly_024 : e0099 = deltaPoly (⟨2, by decide⟩ : Fin 4) := by rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0090
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0090
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0090_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0091
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0091
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0091_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_baseB_020
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_baseB_020
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0092
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0092
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0092_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0093
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0093
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0093_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0094
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0094
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0094_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0095
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0095
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0095_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_fieldPolynomial_021
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_fieldPolynomial_021
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_gammaPoly_022
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_gammaPoly_022
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0096
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0096
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0096_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0097
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0097
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0097_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0098
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0098
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0098_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0099
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.e0099
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.p0099_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_fieldPolynomial_023
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_fieldPolynomial_023
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_deltaPoly_024
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP5.source_deltaPoly_024
