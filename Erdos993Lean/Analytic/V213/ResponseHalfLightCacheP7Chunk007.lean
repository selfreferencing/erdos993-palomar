module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP7Chunk006

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 70: mul.
def e0070 : Expr := Expr.mul e0069 e0000
def p0070 : Bi := exact_poly_nf_compact% (mul p0069 p0000)
theorem p0070_op : p0070 = mul p0069 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0070_encode : p0070 = Expr.encode e0070 [[0,1]] [[],[1]] := by
  rw [p0070_op]
  exact congrArg₂ mul p0069_encode p0000_encode

-- Source node 71: add.
def e0071 : Expr := Expr.add e0068 e0070
def p0071 : Bi := exact_poly_nf_compact% (Bi.add p0068 p0070)
theorem p0071_op : p0071 = Bi.add p0068 p0070 := by decide +kernel
theorem p0071_encode : p0071 = Expr.encode e0071 [[0,1]] [[],[1]] := by
  rw [p0071_op]
  exact congrArg₂ Bi.add p0068_encode p0070_encode

theorem source_fieldPolynomial_015 : e0071 = fieldPolynomial (⟨3, by decide⟩ : Fin 4) (rowData (⟨3, by decide⟩ : Fin 4)).beta0 (rowData (⟨3, by decide⟩ : Fin 4)).beta1 := by rfl

theorem source_betaPoly_016 : e0071 = betaPoly (⟨3, by decide⟩ : Fin 4) := by rfl

-- Source node 72: mul.
def e0072 : Expr := Expr.mul e0003 e0071
def p0072 : Bi := exact_poly_nf_compact% (mul p0003 p0071)
theorem p0072_op : p0072 = mul p0003 p0071 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0072_encode : p0072 = Expr.encode e0072 [[0,1]] [[],[1]] := by
  rw [p0072_op]
  exact congrArg₂ mul p0003_encode p0071_encode

-- Source node 73: mul.
def e0073 : Expr := Expr.mul e0072 e0023
def p0073 : Bi := exact_poly_nf_compact% (mul p0072 p0023)
theorem p0073_op : p0073 = mul p0072 p0023 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0073_encode : p0073 = Expr.encode e0073 [[0,1]] [[],[1]] := by
  rw [p0073_op]
  exact congrArg₂ mul p0072_encode p0023_encode

-- Source node 74: mul.
def e0074 : Expr := Expr.mul e0073 e0002
def p0074 : Bi := exact_poly_nf_compact% (mul p0073 p0002)
theorem p0074_op : p0074 = mul p0073 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0074_encode : p0074 = Expr.encode e0074 [[0,1]] [[],[1]] := by
  rw [p0074_op]
  exact congrArg₂ mul p0073_encode p0002_encode

-- Source node 75: mul.
def e0075 : Expr := Expr.mul e0074 e0006
def p0075 : Bi := exact_poly_nf_compact% (mul p0074 p0006)
theorem p0075_op : p0075 = mul p0074 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0075_encode : p0075 = Expr.encode e0075 [[0,1]] [[],[1]] := by
  rw [p0075_op]
  exact congrArg₂ mul p0074_encode p0006_encode

-- Source node 76: mul.
def e0076 : Expr := Expr.mul e0075 e0028
def p0076 : Bi := exact_poly_nf_compact% (mul p0075 p0028)
theorem p0076_op : p0076 = mul p0075 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0076_encode : p0076 = Expr.encode e0076 [[0,1]] [[],[1]] := by
  rw [p0076_op]
  exact congrArg₂ mul p0075_encode p0028_encode

-- Source node 77: mul.
def e0077 : Expr := Expr.mul e0076 e0004
def p0077 : Bi := exact_poly_nf_compact% (mul p0076 p0004)
theorem p0077_op : p0077 = mul p0076 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0077_encode : p0077 = Expr.encode e0077 [[0,1]] [[],[1]] := by
  rw [p0077_op]
  exact congrArg₂ mul p0076_encode p0004_encode

-- Source node 78: add.
def e0078 : Expr := Expr.add e0067 e0077
def p0078 : Bi := exact_poly_nf_compact% (Bi.add p0067 p0077)
theorem p0078_op : p0078 = Bi.add p0067 p0077 := by decide +kernel
theorem p0078_encode : p0078 = Expr.encode e0078 [[0,1]] [[],[1]] := by
  rw [p0078_op]
  exact congrArg₂ Bi.add p0067_encode p0077_encode

-- Source node 79: mul.
def e0079 : Expr := Expr.mul e0008 e0035
def p0079 : Bi := exact_poly_nf_compact% (mul p0008 p0035)
theorem p0079_op : p0079 = mul p0008 p0035 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0079_encode : p0079 = Expr.encode e0079 [[0,1]] [[],[1]] := by
  rw [p0079_op]
  exact congrArg₂ mul p0008_encode p0035_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0070
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0070
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0070_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0071
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0071
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0071_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.source_fieldPolynomial_015
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.source_fieldPolynomial_015
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.source_betaPoly_016
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.source_betaPoly_016
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0072
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0072
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0072_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0073
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0073
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0073_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0074
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0074
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0074_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0075
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0075
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0075_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0076
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0076
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0076_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0077
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0077
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0077_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0078
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0078
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0078_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0079
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0079
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0079_encode
