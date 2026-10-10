module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Chunk008

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 90: constant.
def e0090 : Expr := Expr.constant (((((rowData (⟨3, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0090 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨3, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0090_op : p0090 = ([[(((((rowData (⟨3, by decide⟩ : Fin 4)).gamma0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0090_encode : p0090 = Expr.encode e0090 [[0,1]] [[],[1]] := by
  rw [p0090_op]
  rfl

-- Source node 91: constant.
def e0091 : Expr := Expr.constant ((((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)
def p0091 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0091_op : p0091 = ([[((((rowData (⟨3, by decide⟩ : Fin 4)).gamma1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0091_encode : p0091 = Expr.encode e0091 [[0,1]] [[],[1]] := by
  rw [p0091_op]
  rfl

-- Source node 92: mul.
def e0092 : Expr := Expr.mul e0091 e0000
def p0092 : Bi := exact_poly_nf_compact% (mul p0091 p0000)
theorem p0092_op : p0092 = mul p0091 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0092_encode : p0092 = Expr.encode e0092 [[0,1]] [[],[1]] := by
  rw [p0092_op]
  exact congrArg₂ mul p0091_encode p0000_encode

-- Source node 93: add.
def e0093 : Expr := Expr.add e0090 e0092
def p0093 : Bi := exact_poly_nf_compact% (Bi.add p0090 p0092)
theorem p0093_op : p0093 = Bi.add p0090 p0092 := by decide +kernel
theorem p0093_encode : p0093 = Expr.encode e0093 [[0,1]] [[],[1]] := by
  rw [p0093_op]
  exact congrArg₂ Bi.add p0090_encode p0092_encode

theorem source_fieldPolynomial_021 : e0093 = fieldPolynomial (⟨3, by decide⟩ : Fin 4) (rowData (⟨3, by decide⟩ : Fin 4)).gamma0 (rowData (⟨3, by decide⟩ : Fin 4)).gamma1 := by rfl

theorem source_gammaPoly_022 : e0093 = gammaPoly (⟨3, by decide⟩ : Fin 4) := by rfl

-- Source node 94: constant.
def e0094 : Expr := Expr.constant (((((rowData (⟨3, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0094 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨3, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0094_op : p0094 = ([[(((((rowData (⟨3, by decide⟩ : Fin 4)).delta0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0094_encode : p0094 = Expr.encode e0094 [[0,1]] [[],[1]] := by
  rw [p0094_op]
  rfl

-- Source node 95: constant.
def e0095 : Expr := Expr.constant ((((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)
def p0095 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0095_op : p0095 = ([[((((rowData (⟨3, by decide⟩ : Fin 4)).delta1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0095_encode : p0095 = Expr.encode e0095 [[0,1]] [[],[1]] := by
  rw [p0095_op]
  rfl

-- Source node 96: mul.
def e0096 : Expr := Expr.mul e0095 e0000
def p0096 : Bi := exact_poly_nf_compact% (mul p0095 p0000)
theorem p0096_op : p0096 = mul p0095 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0096_encode : p0096 = Expr.encode e0096 [[0,1]] [[],[1]] := by
  rw [p0096_op]
  exact congrArg₂ mul p0095_encode p0000_encode

-- Source node 97: add.
def e0097 : Expr := Expr.add e0094 e0096
def p0097 : Bi := exact_poly_nf_compact% (Bi.add p0094 p0096)
theorem p0097_op : p0097 = Bi.add p0094 p0096 := by decide +kernel
theorem p0097_encode : p0097 = Expr.encode e0097 [[0,1]] [[],[1]] := by
  rw [p0097_op]
  exact congrArg₂ Bi.add p0094_encode p0096_encode

theorem source_fieldPolynomial_023 : e0097 = fieldPolynomial (⟨3, by decide⟩ : Fin 4) (rowData (⟨3, by decide⟩ : Fin 4)).delta0 (rowData (⟨3, by decide⟩ : Fin 4)).delta1 := by rfl

theorem source_deltaPoly_024 : e0097 = deltaPoly (⟨3, by decide⟩ : Fin 4) := by rfl

-- Source node 98: neg.
def e0098 : Expr := Expr.neg e0097
def p0098 : Bi := exact_poly_nf_compact% (neg p0097)
theorem p0098_op : p0098 = neg p0097 := by decide +kernel
theorem p0098_encode : p0098 = Expr.encode e0098 [[0,1]] [[],[1]] := by
  rw [p0098_op]
  exact congrArg neg p0097_encode

-- Source node 99: add.
def e0099 : Expr := Expr.add e0093 e0098
def p0099 : Bi := exact_poly_nf_compact% (Bi.add p0093 p0098)
theorem p0099_op : p0099 = Bi.add p0093 p0098 := by decide +kernel
theorem p0099_encode : p0099 = Expr.encode e0099 [[0,1]] [[],[1]] := by
  rw [p0099_op]
  exact congrArg₂ Bi.add p0093_encode p0098_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0090
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0090
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0090_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0091
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0091
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0091_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0092
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0092
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0092_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0093
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0093
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0093_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_021
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_021
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_gammaPoly_022
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_gammaPoly_022
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0094
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0094
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0094_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0095
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0095
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0095_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0096
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0096
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0096_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0097
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0097
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0097_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_023
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_023
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_deltaPoly_024
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_deltaPoly_024
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0098
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0098
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0098_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0099
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0099
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0099_encode
