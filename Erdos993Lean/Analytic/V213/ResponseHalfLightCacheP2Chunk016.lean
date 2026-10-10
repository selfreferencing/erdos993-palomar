module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Chunk015

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 160: mul.
def e0160 : Expr := Expr.mul e0159 e0019
def p0160 : Bi := exact_poly_nf_compact% (mul p0159 p0019)
theorem p0160_op : p0160 = mul p0159 p0019 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0160_encode : p0160 = Expr.encode e0160 [[0,1]] [[],[1]] := by
  rw [p0160_op]
  exact congrArg₂ mul p0159_encode p0019_encode

-- Source node 161: pow_succ.
def e0161 : Expr := Expr.pow e0028 3
def p0161 : Bi := exact_poly_nf_compact% (mul p0100 p0028)
theorem p0161_op : p0161 = mul p0100 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0161_encode : p0161 = Expr.encode e0161 [[0,1]] [[],[1]] := by
  rw [p0161_op]
  exact congrArg₂ mul p0100_encode p0028_encode

-- Source node 162: mul.
def e0162 : Expr := Expr.mul e0160 e0161
def p0162 : Bi := exact_poly_nf_compact% (mul p0160 p0161)
theorem p0162_op : p0162 = mul p0160 p0161 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0162_encode : p0162 = Expr.encode e0162 [[0,1]] [[],[1]] := by
  rw [p0162_op]
  exact congrArg₂ mul p0160_encode p0161_encode

-- Source node 163: mul.
def e0163 : Expr := Expr.mul e0162 e0001
def p0163 : Bi := exact_poly_nf_compact% (mul p0162 p0001)
theorem p0163_op : p0163 = mul p0162 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0163_encode : p0163 = Expr.encode e0163 [[0,1]] [[],[1]] := by
  rw [p0163_op]
  exact congrArg₂ mul p0162_encode p0001_encode

-- Source node 164: mul.
def e0164 : Expr := Expr.mul e0163 e0004
def p0164 : Bi := exact_poly_nf_compact% (mul p0163 p0004)
theorem p0164_op : p0164 = mul p0163 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0164_encode : p0164 = Expr.encode e0164 [[0,1]] [[],[1]] := by
  rw [p0164_op]
  exact congrArg₂ mul p0163_encode p0004_encode

-- Source node 165: mul.
def e0165 : Expr := Expr.mul e0164 e0038
def p0165 : Bi := exact_poly_nf_compact% (mul p0164 p0038)
theorem p0165_op : p0165 = mul p0164 p0038 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0165_encode : p0165 = Expr.encode e0165 [[0,1]] [[],[1]] := by
  rw [p0165_op]
  exact congrArg₂ mul p0164_encode p0038_encode

-- Source node 166: pow_zero.
def e0166 : Expr := Expr.pow e0086 0
def p0166 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0166_op : p0166 = ([[1]] : Bi) := by decide +kernel
theorem p0166_encode : p0166 = Expr.encode e0166 [[0,1]] [[],[1]] := by
  rw [p0166_op]
  rfl

-- Source node 167: pow_succ.
def e0167 : Expr := Expr.pow e0086 1
def p0167 : Bi := exact_poly_nf_compact% (mul p0166 p0086)
theorem p0167_op : p0167 = mul p0166 p0086 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0167_encode : p0167 = Expr.encode e0167 [[0,1]] [[],[1]] := by
  rw [p0167_op]
  exact congrArg₂ mul p0166_encode p0086_encode

-- Source node 168: pow_succ.
def e0168 : Expr := Expr.pow e0086 2
def p0168 : Bi := exact_poly_nf_compact% (mul p0167 p0086)
theorem p0168_op : p0168 = mul p0167 p0086 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0168_encode : p0168 = Expr.encode e0168 [[0,1]] [[],[1]] := by
  rw [p0168_op]
  exact congrArg₂ mul p0167_encode p0086_encode

-- Source node 169: mul.
def e0169 : Expr := Expr.mul e0165 e0168
def p0169 : Bi := exact_poly_nf_compact% (mul p0165 p0168)
theorem p0169_op : p0169 = mul p0165 p0168 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0169_encode : p0169 = Expr.encode e0169 [[0,1]] [[],[1]] := by
  rw [p0169_op]
  exact congrArg₂ mul p0165_encode p0168_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0160
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0160
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0160_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0161
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0161
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0161_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0162
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0162
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0162_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0163
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0163
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0163_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0164
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0164
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0164_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0165
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0165
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0165_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0166
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0166
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0166_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0167
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0167
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0167_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0168
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0168
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0168_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0169
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0169
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0169_encode
