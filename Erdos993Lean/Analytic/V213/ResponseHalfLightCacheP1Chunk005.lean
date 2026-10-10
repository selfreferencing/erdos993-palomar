module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP1Chunk004

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 50: constant.
def e0050 : Expr := Expr.constant (((((rowData (⟨0, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0050 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨0, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0050_op : p0050 = ([[(((((rowData (⟨0, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨0, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0050_encode : p0050 = Expr.encode e0050 [[0,1]] [[],[1]] := by
  rw [p0050_op]
  rfl

-- Source node 51: constant.
def e0051 : Expr := Expr.constant ((((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)
def p0051 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0051_op : p0051 = ([[((((rowData (⟨0, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0051_encode : p0051 = Expr.encode e0051 [[0,1]] [[],[1]] := by
  rw [p0051_op]
  rfl

-- Source node 52: mul.
def e0052 : Expr := Expr.mul e0051 e0000
def p0052 : Bi := exact_poly_nf_compact% (mul p0051 p0000)
theorem p0052_op : p0052 = mul p0051 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0052_encode : p0052 = Expr.encode e0052 [[0,1]] [[],[1]] := by
  rw [p0052_op]
  exact congrArg₂ mul p0051_encode p0000_encode

-- Source node 53: add.
def e0053 : Expr := Expr.add e0050 e0052
def p0053 : Bi := exact_poly_nf_compact% (Bi.add p0050 p0052)
theorem p0053_op : p0053 = Bi.add p0050 p0052 := by decide +kernel
theorem p0053_encode : p0053 = Expr.encode e0053 [[0,1]] [[],[1]] := by
  rw [p0053_op]
  exact congrArg₂ Bi.add p0050_encode p0052_encode

theorem source_fieldPolynomial_013 : e0053 = fieldPolynomial (⟨0, by decide⟩ : Fin 4) (rowData (⟨0, by decide⟩ : Fin 4)).alpha0 (rowData (⟨0, by decide⟩ : Fin 4)).alpha1 := by rfl

theorem source_alphaPoly_014 : e0053 = alphaPoly (⟨0, by decide⟩ : Fin 4) := by rfl

-- Source node 54: mul.
def e0054 : Expr := Expr.mul e0007 e0053
def p0054 : Bi := exact_poly_nf_compact% (mul p0007 p0053)
theorem p0054_op : p0054 = mul p0007 p0053 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0054_encode : p0054 = Expr.encode e0054 [[0,1]] [[],[1]] := by
  rw [p0054_op]
  exact congrArg₂ mul p0007_encode p0053_encode

-- Source node 55: mul.
def e0055 : Expr := Expr.mul e0054 e0000
def p0055 : Bi := exact_poly_nf_compact% (mul p0054 p0000)
theorem p0055_op : p0055 = mul p0054 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0055_encode : p0055 = Expr.encode e0055 [[0,1]] [[],[1]] := by
  rw [p0055_op]
  exact congrArg₂ mul p0054_encode p0000_encode

-- Source node 56: mul.
def e0056 : Expr := Expr.mul e0055 e0035
def p0056 : Bi := exact_poly_nf_compact% (mul p0055 p0035)
theorem p0056_op : p0056 = mul p0055 p0035 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0056_encode : p0056 = Expr.encode e0056 [[0,1]] [[],[1]] := by
  rw [p0056_op]
  exact congrArg₂ mul p0055_encode p0035_encode

-- Source node 57: mul.
def e0057 : Expr := Expr.mul e0056 e0006
def p0057 : Bi := exact_poly_nf_compact% (mul p0056 p0006)
theorem p0057_op : p0057 = mul p0056 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0057_encode : p0057 = Expr.encode e0057 [[0,1]] [[],[1]] := by
  rw [p0057_op]
  exact congrArg₂ mul p0056_encode p0006_encode

-- Source node 58: mul.
def e0058 : Expr := Expr.mul e0057 e0028
def p0058 : Bi := exact_poly_nf_compact% (mul p0057 p0028)
theorem p0058_op : p0058 = mul p0057 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0058_encode : p0058 = Expr.encode e0058 [[0,1]] [[],[1]] := by
  rw [p0058_op]
  exact congrArg₂ mul p0057_encode p0028_encode

-- Source node 59: neg.
def e0059 : Expr := Expr.neg e0058
def p0059 : Bi := exact_poly_nf_compact% (neg p0058)
theorem p0059_op : p0059 = neg p0058 := by decide +kernel
theorem p0059_encode : p0059 = Expr.encode e0059 [[0,1]] [[],[1]] := by
  rw [p0059_op]
  exact congrArg neg p0058_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0050
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0050
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0050_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0051
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0051
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0051_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0052
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0052
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0052_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0053
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0053
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0053_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_fieldPolynomial_013
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_fieldPolynomial_013
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_alphaPoly_014
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_alphaPoly_014
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0054
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0054
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0054_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0055
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0055
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0055_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0056
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0056
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0056_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0057
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0057
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0057_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0058
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0058
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0058_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0059
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0059
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0059_encode
