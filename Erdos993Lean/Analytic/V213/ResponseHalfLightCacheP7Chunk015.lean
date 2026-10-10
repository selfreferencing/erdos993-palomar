module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP7Chunk014

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 150: mul.
def e0150 : Expr := Expr.mul e0149 e0110
def p0150 : Bi := exact_poly_nf_compact% (mul p0149 p0110)
theorem p0150_op : p0150 = mul p0149 p0110 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0150_encode : p0150 = Expr.encode e0150 [[0,1]] [[],[1]] := by
  rw [p0150_op]
  exact congrArg₂ mul p0149_encode p0110_encode

-- Source node 151: pow_zero.
def e0151 : Expr := Expr.pow e0084 0
def p0151 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0151_op : p0151 = ([[1]] : Bi) := by decide +kernel
theorem p0151_encode : p0151 = Expr.encode e0151 [[0,1]] [[],[1]] := by
  rw [p0151_op]
  rfl

-- Source node 152: pow_succ.
def e0152 : Expr := Expr.pow e0084 1
def p0152 : Bi := exact_poly_nf_compact% (mul p0151 p0084)
theorem p0152_op : p0152 = mul p0151 p0084 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0152_encode : p0152 = Expr.encode e0152 [[0,1]] [[],[1]] := by
  rw [p0152_op]
  exact congrArg₂ mul p0151_encode p0084_encode

-- Source node 153: pow_succ.
def e0153 : Expr := Expr.pow e0084 2
def p0153 : Bi := exact_poly_nf_compact% (mul p0152 p0084)
theorem p0153_op : p0153 = mul p0152 p0084 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0153_encode : p0153 = Expr.encode e0153 [[0,1]] [[],[1]] := by
  rw [p0153_op]
  exact congrArg₂ mul p0152_encode p0084_encode

-- Source node 154: mul.
def e0154 : Expr := Expr.mul e0150 e0153
def p0154 : Bi := exact_poly_nf_compact% (mul p0150 p0153)
theorem p0154_op : p0154 = mul p0150 p0153 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0154_encode : p0154 = Expr.encode e0154 [[0,1]] [[],[1]] := by
  rw [p0154_op]
  exact congrArg₂ mul p0150_encode p0153_encode

-- Source node 155: neg.
def e0155 : Expr := Expr.neg e0154
def p0155 : Bi := exact_poly_nf_compact% (neg p0154)
theorem p0155_op : p0155 = neg p0154 := by decide +kernel
theorem p0155_encode : p0155 = Expr.encode e0155 [[0,1]] [[],[1]] := by
  rw [p0155_op]
  exact congrArg neg p0154_encode

-- Source node 156: add.
def e0156 : Expr := Expr.add e0142 e0155
def p0156 : Bi := exact_poly_nf_compact% (Bi.add p0142 p0155)
theorem p0156_op : p0156 = Bi.add p0142 p0155 := by decide +kernel
theorem p0156_encode : p0156 = Expr.encode e0156 [[0,1]] [[],[1]] := by
  rw [p0156_op]
  exact congrArg₂ Bi.add p0142_encode p0155_encode

-- Source node 157: constant.
def e0157 : Expr := Expr.constant ((1/8) : ℚ)
def p0157 : Bi := exact_poly_nf_compact% (([[((1/8) : ℚ)]] : Bi))
theorem p0157_op : p0157 = ([[((1/8) : ℚ)]] : Bi) := by decide +kernel
theorem p0157_encode : p0157 = Expr.encode e0157 [[0,1]] [[],[1]] := by
  rw [p0157_op]
  rfl

-- Source node 158: pow_succ.
def e0158 : Expr := Expr.pow e0000 3
def p0158 : Bi := exact_poly_nf_compact% (mul p0023 p0000)
theorem p0158_op : p0158 = mul p0023 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0158_encode : p0158 = Expr.encode e0158 [[0,1]] [[],[1]] := by
  rw [p0158_op]
  exact congrArg₂ mul p0023_encode p0000_encode

-- Source node 159: pow_succ.
def e0159 : Expr := Expr.pow e0000 4
def p0159 : Bi := exact_poly_nf_compact% (mul p0158 p0000)
theorem p0159_op : p0159 = mul p0158 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0159_encode : p0159 = Expr.encode e0159 [[0,1]] [[],[1]] := by
  rw [p0159_op]
  exact congrArg₂ mul p0158_encode p0000_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0150
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0150
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0150_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0151
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0151
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0151_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0152
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0152
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0152_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0153
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0153
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0153_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0154
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0154
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0154_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0155
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0155
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0155_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0156
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0156
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0156_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0157
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0157
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0157_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0158
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0158
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0158_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0159
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0159
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0159_encode
