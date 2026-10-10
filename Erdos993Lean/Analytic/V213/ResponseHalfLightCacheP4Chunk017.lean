module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP4Chunk016

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 170: neg.
def e0170 : Expr := Expr.neg e0169
def p0170 : Bi := exact_poly_nf_compact% (neg p0169)
theorem p0170_op : p0170 = neg p0169 := by decide +kernel
theorem p0170_encode : p0170 = Expr.encode e0170 [[0,1]] [[],[1]] := by
  rw [p0170_op]
  exact congrArg neg p0169_encode

-- Source node 171: add.
def e0171 : Expr := Expr.add e0151 e0170
def p0171 : Bi := exact_poly_nf_compact% (Bi.add p0151 p0170)
theorem p0171_op : p0171 = Bi.add p0151 p0170 := by decide +kernel
theorem p0171_encode : p0171 = Expr.encode e0171 [[0,1]] [[],[1]] := by
  rw [p0171_op]
  exact congrArg₂ Bi.add p0151_encode p0170_encode

-- Source node 172: constant.
def e0172 : Expr := Expr.constant ((1/2) : ℚ)
def p0172 : Bi := exact_poly_nf_compact% (([[((1/2) : ℚ)]] : Bi))
theorem p0172_op : p0172 = ([[((1/2) : ℚ)]] : Bi) := by decide +kernel
theorem p0172_encode : p0172 = Expr.encode e0172 [[0,1]] [[],[1]] := by
  rw [p0172_op]
  rfl

-- Source node 173: mul.
def e0173 : Expr := Expr.mul e0172 e0154
def p0173 : Bi := exact_poly_nf_compact% (mul p0172 p0154)
theorem p0173_op : p0173 = mul p0172 p0154 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0173_encode : p0173 = Expr.encode e0173 [[0,1]] [[],[1]] := by
  rw [p0173_op]
  exact congrArg₂ mul p0172_encode p0154_encode

-- Source node 174: mul.
def e0174 : Expr := Expr.mul e0173 e0058
def p0174 : Bi := exact_poly_nf_compact% (mul p0173 p0058)
theorem p0174_op : p0174 = mul p0173 p0058 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0174_encode : p0174 = Expr.encode e0174 [[0,1]] [[],[1]] := by
  rw [p0174_op]
  exact congrArg₂ mul p0173_encode p0058_encode

-- Source node 175: mul.
def e0175 : Expr := Expr.mul e0174 e0006
def p0175 : Bi := exact_poly_nf_compact% (mul p0174 p0006)
theorem p0175_op : p0175 = mul p0174 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0175_encode : p0175 = Expr.encode e0175 [[0,1]] [[],[1]] := by
  rw [p0175_op]
  exact congrArg₂ mul p0174_encode p0006_encode

-- Source node 176: mul.
def e0176 : Expr := Expr.mul e0175 e0001
def p0176 : Bi := exact_poly_nf_compact% (mul p0175 p0001)
theorem p0176_op : p0176 = mul p0175 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0176_encode : p0176 = Expr.encode e0176 [[0,1]] [[],[1]] := by
  rw [p0176_op]
  exact congrArg₂ mul p0175_encode p0001_encode

-- Source node 177: mul.
def e0177 : Expr := Expr.mul e0176 e0012
def p0177 : Bi := exact_poly_nf_compact% (mul p0176 p0012)
theorem p0177_op : p0177 = mul p0176 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0177_encode : p0177 = Expr.encode e0177 [[0,1]] [[],[1]] := by
  rw [p0177_op]
  exact congrArg₂ mul p0176_encode p0012_encode

-- Source node 178: mul.
def e0178 : Expr := Expr.mul e0177 e0019
def p0178 : Bi := exact_poly_nf_compact% (mul p0177 p0019)
theorem p0178_op : p0178 = mul p0177 p0019 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0178_encode : p0178 = Expr.encode e0178 [[0,1]] [[],[1]] := by
  rw [p0178_op]
  exact congrArg₂ mul p0177_encode p0019_encode

-- Source node 179: mul.
def e0179 : Expr := Expr.mul e0178 e0100
def p0179 : Bi := exact_poly_nf_compact% (mul p0178 p0100)
theorem p0179_op : p0179 = mul p0178 p0100 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0179_encode : p0179 = Expr.encode e0179 [[0,1]] [[],[1]] := by
  rw [p0179_op]
  exact congrArg₂ mul p0178_encode p0100_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0170
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0170
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0170_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0171
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0171
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0171_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0172
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0172
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0172_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0173
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0173
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0173_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0174
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0174
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0174_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0175
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0175
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0175_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0176
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0176
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0176_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0177
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0177
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0177_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0178
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0178
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0178_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0179
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0179
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0179_encode
