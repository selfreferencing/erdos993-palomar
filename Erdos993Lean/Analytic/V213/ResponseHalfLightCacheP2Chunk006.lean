module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Chunk005

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 60: mul.
def e0060 : Expr := Expr.mul e0059 e0001
def p0060 : Bi := exact_poly_nf_compact% (mul p0059 p0001)
theorem p0060_op : p0060 = mul p0059 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0060_encode : p0060 = Expr.encode e0060 [[0,1]] [[],[1]] := by
  rw [p0060_op]
  exact congrArg₂ mul p0059_encode p0001_encode

-- Source node 61: neg.
def e0061 : Expr := Expr.neg e0060
def p0061 : Bi := exact_poly_nf_compact% (neg p0060)
theorem p0061_op : p0061 = neg p0060 := by decide +kernel
theorem p0061_encode : p0061 = Expr.encode e0061 [[0,1]] [[],[1]] := by
  rw [p0061_op]
  exact congrArg neg p0060_encode

-- Source node 62: add.
def e0062 : Expr := Expr.add e0055 e0061
def p0062 : Bi := exact_poly_nf_compact% (Bi.add p0055 p0061)
theorem p0062_op : p0062 = Bi.add p0055 p0061 := by decide +kernel
theorem p0062_encode : p0062 = Expr.encode e0062 [[0,1]] [[],[1]] := by
  rw [p0062_op]
  exact congrArg₂ Bi.add p0055_encode p0061_encode

-- Source node 63: constant.
def e0063 : Expr := Expr.constant (((((rowData (⟨1, by decide⟩ : Fin 4)).beta0:ℚ)-((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)*(rowData (⟨1, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0063 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨1, by decide⟩ : Fin 4)).beta0:ℚ)-((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)*(rowData (⟨1, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0063_op : p0063 = ([[(((((rowData (⟨1, by decide⟩ : Fin 4)).beta0:ℚ)-((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)*(rowData (⟨1, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0063_encode : p0063 = Expr.encode e0063 [[0,1]] [[],[1]] := by
  rw [p0063_op]
  rfl

-- Source node 64: constant.
def e0064 : Expr := Expr.constant ((((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)/65536) : ℚ)
def p0064 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0064_op : p0064 = ([[((((rowData (⟨1, by decide⟩ : Fin 4)).beta1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0064_encode : p0064 = Expr.encode e0064 [[0,1]] [[],[1]] := by
  rw [p0064_op]
  rfl

-- Source node 65: mul.
def e0065 : Expr := Expr.mul e0064 e0000
def p0065 : Bi := exact_poly_nf_compact% (mul p0064 p0000)
theorem p0065_op : p0065 = mul p0064 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0065_encode : p0065 = Expr.encode e0065 [[0,1]] [[],[1]] := by
  rw [p0065_op]
  exact congrArg₂ mul p0064_encode p0000_encode

-- Source node 66: add.
def e0066 : Expr := Expr.add e0063 e0065
def p0066 : Bi := exact_poly_nf_compact% (Bi.add p0063 p0065)
theorem p0066_op : p0066 = Bi.add p0063 p0065 := by decide +kernel
theorem p0066_encode : p0066 = Expr.encode e0066 [[0,1]] [[],[1]] := by
  rw [p0066_op]
  exact congrArg₂ Bi.add p0063_encode p0065_encode

theorem source_fieldPolynomial_015 : e0066 = fieldPolynomial (⟨1, by decide⟩ : Fin 4) (rowData (⟨1, by decide⟩ : Fin 4)).beta0 (rowData (⟨1, by decide⟩ : Fin 4)).beta1 := by rfl

theorem source_betaPoly_016 : e0066 = betaPoly (⟨1, by decide⟩ : Fin 4) := by rfl

-- Source node 67: mul.
def e0067 : Expr := Expr.mul e0003 e0066
def p0067 : Bi := exact_poly_nf_compact% (mul p0003 p0066)
theorem p0067_op : p0067 = mul p0003 p0066 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0067_encode : p0067 = Expr.encode e0067 [[0,1]] [[],[1]] := by
  rw [p0067_op]
  exact congrArg₂ mul p0003_encode p0066_encode

-- Source node 68: mul.
def e0068 : Expr := Expr.mul e0067 e0023
def p0068 : Bi := exact_poly_nf_compact% (mul p0067 p0023)
theorem p0068_op : p0068 = mul p0067 p0023 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0068_encode : p0068 = Expr.encode e0068 [[0,1]] [[],[1]] := by
  rw [p0068_op]
  exact congrArg₂ mul p0067_encode p0023_encode

-- Source node 69: mul.
def e0069 : Expr := Expr.mul e0068 e0002
def p0069 : Bi := exact_poly_nf_compact% (mul p0068 p0002)
theorem p0069_op : p0069 = mul p0068 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0069_encode : p0069 = Expr.encode e0069 [[0,1]] [[],[1]] := by
  rw [p0069_op]
  exact congrArg₂ mul p0068_encode p0002_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0060
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0060
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0060_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0061
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0061
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0061_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0062
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0062
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0062_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0063
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0063
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0063_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0064
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0064
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0064_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0065
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0065
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0065_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0066
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0066
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0066_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_fieldPolynomial_015
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_fieldPolynomial_015
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_betaPoly_016
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.source_betaPoly_016
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0067
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0067
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0067_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0068
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0068
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0068_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0069
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0069
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0069_encode
