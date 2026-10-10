module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP3Chunk016

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 170: mul.
def e0170 : Expr := Expr.mul e0169 e0042
def p0170 : Bi := exact_poly_nf_compact% (mul p0169 p0042)
theorem p0170_op : p0170 = mul p0169 p0042 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0170_encode : p0170 = Expr.encode e0170 [[0,1]] [[],[1]] := by
  rw [p0170_op]
  exact congrArg₂ mul p0169_encode p0042_encode

-- Source node 171: pow_zero.
def e0171 : Expr := Expr.pow e0091 0
def p0171 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0171_op : p0171 = ([[1]] : Bi) := by decide +kernel
theorem p0171_encode : p0171 = Expr.encode e0171 [[0,1]] [[],[1]] := by
  rw [p0171_op]
  rfl

-- Source node 172: pow_succ.
def e0172 : Expr := Expr.pow e0091 1
def p0172 : Bi := exact_poly_nf_compact% (mul p0171 p0091)
theorem p0172_op : p0172 = mul p0171 p0091 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0172_encode : p0172 = Expr.encode e0172 [[0,1]] [[],[1]] := by
  rw [p0172_op]
  exact congrArg₂ mul p0171_encode p0091_encode

-- Source node 173: pow_succ.
def e0173 : Expr := Expr.pow e0091 2
def p0173 : Bi := exact_poly_nf_compact% (mul p0172 p0091)
theorem p0173_op : p0173 = mul p0172 p0091 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0173_encode : p0173 = Expr.encode e0173 [[0,1]] [[],[1]] := by
  rw [p0173_op]
  exact congrArg₂ mul p0172_encode p0091_encode

-- Source node 174: mul.
def e0174 : Expr := Expr.mul e0170 e0173
def p0174 : Bi := exact_poly_nf_compact% (mul p0170 p0173)
theorem p0174_op : p0174 = mul p0170 p0173 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0174_encode : p0174 = Expr.encode e0174 [[0,1]] [[],[1]] := by
  rw [p0174_op]
  exact congrArg₂ mul p0170_encode p0173_encode

-- Source node 175: neg.
def e0175 : Expr := Expr.neg e0174
def p0175 : Bi := exact_poly_nf_compact% (neg p0174)
theorem p0175_op : p0175 = neg p0174 := by decide +kernel
theorem p0175_encode : p0175 = Expr.encode e0175 [[0,1]] [[],[1]] := by
  rw [p0175_op]
  exact congrArg neg p0174_encode

-- Source node 176: add.
def e0176 : Expr := Expr.add e0156 e0175
def p0176 : Bi := exact_poly_nf_compact% (Bi.add p0156 p0175)
theorem p0176_op : p0176 = Bi.add p0156 p0175 := by decide +kernel
theorem p0176_encode : p0176 = Expr.encode e0176 [[0,1]] [[],[1]] := by
  rw [p0176_op]
  exact congrArg₂ Bi.add p0156_encode p0175_encode

-- Source node 177: constant.
def e0177 : Expr := Expr.constant ((1/2) : ℚ)
def p0177 : Bi := exact_poly_nf_compact% (([[((1/2) : ℚ)]] : Bi))
theorem p0177_op : p0177 = ([[((1/2) : ℚ)]] : Bi) := by decide +kernel
theorem p0177_encode : p0177 = Expr.encode e0177 [[0,1]] [[],[1]] := by
  rw [p0177_op]
  rfl

-- Source node 178: mul.
def e0178 : Expr := Expr.mul e0177 e0159
def p0178 : Bi := exact_poly_nf_compact% (mul p0177 p0159)
theorem p0178_op : p0178 = mul p0177 p0159 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0178_encode : p0178 = Expr.encode e0178 [[0,1]] [[],[1]] := by
  rw [p0178_op]
  exact congrArg₂ mul p0177_encode p0159_encode

-- Source node 179: mul.
def e0179 : Expr := Expr.mul e0178 e0063
def p0179 : Bi := exact_poly_nf_compact% (mul p0178 p0063)
theorem p0179_op : p0179 = mul p0178 p0063 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0179_encode : p0179 = Expr.encode e0179 [[0,1]] [[],[1]] := by
  rw [p0179_op]
  exact congrArg₂ mul p0178_encode p0063_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0170
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0170
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0170_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0171
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0171
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0171_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0172
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0172
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0172_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0173
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0173
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0173_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0174
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0174
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0174_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0175
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0175
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0175_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0176
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0176
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0176_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0177
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0177
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0177_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0178
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0178
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0178_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0179
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.e0179
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP3.p0179_encode
