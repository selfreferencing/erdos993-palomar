module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP6Chunk003

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 40: neg.
def e0040 : Expr := Expr.neg e0032
def p0040 : Bi := exact_poly_nf_compact% (neg p0032)
theorem p0040_op : p0040 = neg p0032 := by decide +kernel
theorem p0040_encode : p0040 = Expr.encode e0040 [[0,1]] [[],[1]] := by
  rw [p0040_op]
  exact congrArg neg p0032_encode

-- Source node 41: mul.
def e0041 : Expr := Expr.mul e0040 e0030
def p0041 : Bi := exact_poly_nf_compact% (mul p0040 p0030)
theorem p0041_op : p0041 = mul p0040 p0030 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0041_encode : p0041 = Expr.encode e0041 [[0,1]] [[],[1]] := by
  rw [p0041_op]
  exact congrArg₂ mul p0040_encode p0030_encode

-- Source node 42: mul.
def e0042 : Expr := Expr.mul e0041 e0028
def p0042 : Bi := exact_poly_nf_compact% (mul p0041 p0028)
theorem p0042_op : p0042 = mul p0041 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0042_encode : p0042 = Expr.encode e0042 [[0,1]] [[],[1]] := by
  rw [p0042_op]
  exact congrArg₂ mul p0041_encode p0028_encode

theorem source_sourceBNum_012 : e0042 = sourceBNum (⟨3, by decide⟩ : Fin 4) 1 := by rfl

-- Source node 43: constant.
def e0043 : Expr := Expr.constant (((((rowData (⟨3, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)
def p0043 : Bi := exact_poly_nf_compact% (([[(((((rowData (⟨3, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi))
theorem p0043_op : p0043 = ([[(((((rowData (⟨3, by decide⟩ : Fin 4)).alpha0:ℚ)-((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)*(rowData (⟨3, by decide⟩ : Fin 4)).center)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0043_encode : p0043 = Expr.encode e0043 [[0,1]] [[],[1]] := by
  rw [p0043_op]
  rfl

-- Source node 44: constant.
def e0044 : Expr := Expr.constant ((((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)
def p0044 : Bi := exact_poly_nf_compact% (([[((((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)]] : Bi))
theorem p0044_op : p0044 = ([[((((rowData (⟨3, by decide⟩ : Fin 4)).alpha1:ℚ)/65536) : ℚ)]] : Bi) := by decide +kernel
theorem p0044_encode : p0044 = Expr.encode e0044 [[0,1]] [[],[1]] := by
  rw [p0044_op]
  rfl

-- Source node 45: mul.
def e0045 : Expr := Expr.mul e0044 e0000
def p0045 : Bi := exact_poly_nf_compact% (mul p0044 p0000)
theorem p0045_op : p0045 = mul p0044 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0045_encode : p0045 = Expr.encode e0045 [[0,1]] [[],[1]] := by
  rw [p0045_op]
  exact congrArg₂ mul p0044_encode p0000_encode

-- Source node 46: add.
def e0046 : Expr := Expr.add e0043 e0045
def p0046 : Bi := exact_poly_nf_compact% (Bi.add p0043 p0045)
theorem p0046_op : p0046 = Bi.add p0043 p0045 := by decide +kernel
theorem p0046_encode : p0046 = Expr.encode e0046 [[0,1]] [[],[1]] := by
  rw [p0046_op]
  exact congrArg₂ Bi.add p0043_encode p0045_encode

theorem source_fieldPolynomial_013 : e0046 = fieldPolynomial (⟨3, by decide⟩ : Fin 4) (rowData (⟨3, by decide⟩ : Fin 4)).alpha0 (rowData (⟨3, by decide⟩ : Fin 4)).alpha1 := by rfl

theorem source_alphaPoly_014 : e0046 = alphaPoly (⟨3, by decide⟩ : Fin 4) := by rfl

-- Source node 47: mul.
def e0047 : Expr := Expr.mul e0007 e0046
def p0047 : Bi := exact_poly_nf_compact% (mul p0007 p0046)
theorem p0047_op : p0047 = mul p0007 p0046 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0047_encode : p0047 = Expr.encode e0047 [[0,1]] [[],[1]] := by
  rw [p0047_op]
  exact congrArg₂ mul p0007_encode p0046_encode

-- Source node 48: mul.
def e0048 : Expr := Expr.mul e0047 e0000
def p0048 : Bi := exact_poly_nf_compact% (mul p0047 p0000)
theorem p0048_op : p0048 = mul p0047 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0048_encode : p0048 = Expr.encode e0048 [[0,1]] [[],[1]] := by
  rw [p0048_op]
  exact congrArg₂ mul p0047_encode p0000_encode

-- Source node 49: pow_zero.
def e0049 : Expr := Expr.pow e0002 0
def p0049 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0049_op : p0049 = ([[1]] : Bi) := by decide +kernel
theorem p0049_encode : p0049 = Expr.encode e0049 [[0,1]] [[],[1]] := by
  rw [p0049_op]
  rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0040
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0040
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0040_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0041
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0041
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0041_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0042
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0042
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0042_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_sourceBNum_012
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_sourceBNum_012
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0043
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0043
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0043_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0044
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0044
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0044_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0045
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0045
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0045_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0046
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0046
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0046_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_013
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_fieldPolynomial_013
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_alphaPoly_014
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.source_alphaPoly_014
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0047
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0047
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0047_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0048
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0048
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0048_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0049
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.e0049
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP6.p0049_encode
