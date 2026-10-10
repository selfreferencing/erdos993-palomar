module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP0Chunk017

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 180: mul.
def e0180 : Expr := Expr.mul e0179 e0001
def p0180 : Bi := exact_poly_nf_compact% (mul p0179 p0001)
theorem p0180_op : p0180 = mul p0179 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0180_encode : p0180 = Expr.encode e0180 [[0,1]] [[],[1]] := by
  rw [p0180_op]
  exact congrArg₂ mul p0179_encode p0001_encode

-- Source node 181: mul.
def e0181 : Expr := Expr.mul e0180 e0004
def p0181 : Bi := exact_poly_nf_compact% (mul p0180 p0004)
theorem p0181_op : p0181 = mul p0180 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0181_encode : p0181 = Expr.encode e0181 [[0,1]] [[],[1]] := by
  rw [p0181_op]
  exact congrArg₂ mul p0180_encode p0004_encode

-- Source node 182: mul.
def e0182 : Expr := Expr.mul e0181 e0079
def p0182 : Bi := exact_poly_nf_compact% (mul p0181 p0079)
theorem p0182_op : p0182 = mul p0181 p0079 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0182_encode : p0182 = Expr.encode e0182 [[0,1]] [[],[1]] := by
  rw [p0182_op]
  exact congrArg₂ mul p0181_encode p0079_encode

-- Source node 183: mul.
def e0183 : Expr := Expr.mul e0182 e0086
def p0183 : Bi := exact_poly_nf_compact% (mul p0182 p0086)
theorem p0183_op : p0183 = mul p0182 p0086 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0183_encode : p0183 = Expr.encode e0183 [[0,1]] [[],[1]] := by
  rw [p0183_op]
  exact congrArg₂ mul p0182_encode p0086_encode

-- Source node 184: add.
def e0184 : Expr := Expr.add e0171 e0183
def p0184 : Bi := exact_poly_nf_compact% (Bi.add p0171 p0183)
theorem p0184_op : p0184 = Bi.add p0171 p0183 := by decide +kernel
theorem p0184_encode : p0184 = Expr.encode e0184 [[0,1]] [[],[1]] := by
  rw [p0184_op]
  exact congrArg₂ Bi.add p0171_encode p0183_encode

-- Source node 185: pow_succ.
def e0185 : Expr := Expr.pow e0000 5
def p0185 : Bi := exact_poly_nf_compact% (mul p0154 p0000)
theorem p0185_op : p0185 = mul p0154 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0185_encode : p0185 = Expr.encode e0185 [[0,1]] [[],[1]] := by
  rw [p0185_op]
  exact congrArg₂ mul p0154_encode p0000_encode

-- Source node 186: mul.
def e0186 : Expr := Expr.mul e0056 e0185
def p0186 : Bi := exact_poly_nf_compact% (mul p0056 p0185)
theorem p0186_op : p0186 = mul p0056 p0185 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0186_encode : p0186 = Expr.encode e0186 [[0,1]] [[],[1]] := by
  rw [p0186_op]
  exact congrArg₂ mul p0056_encode p0185_encode

-- Source node 187: pow_succ.
def e0187 : Expr := Expr.pow e0002 4
def p0187 : Bi := exact_poly_nf_compact% (mul p0058 p0002)
theorem p0187_op : p0187 = mul p0058 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0187_encode : p0187 = Expr.encode e0187 [[0,1]] [[],[1]] := by
  rw [p0187_op]
  exact congrArg₂ mul p0058_encode p0002_encode

-- Source node 188: pow_succ.
def e0188 : Expr := Expr.pow e0002 5
def p0188 : Bi := exact_poly_nf_compact% (mul p0187 p0002)
theorem p0188_op : p0188 = mul p0187 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0188_encode : p0188 = Expr.encode e0188 [[0,1]] [[],[1]] := by
  rw [p0188_op]
  exact congrArg₂ mul p0187_encode p0002_encode

-- Source node 189: pow_succ.
def e0189 : Expr := Expr.pow e0002 6
def p0189 : Bi := exact_poly_nf_compact% (mul p0188 p0002)
theorem p0189_op : p0189 = mul p0188 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0189_encode : p0189 = Expr.encode e0189 [[0,1]] [[],[1]] := by
  rw [p0189_op]
  exact congrArg₂ mul p0188_encode p0002_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0180
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0180
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0180_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0181
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0181
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0181_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0182
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0182
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0182_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0183
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0183
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0183_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0184
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0184
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0184_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0185
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0185
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0185_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0186
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0186
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0186_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0187
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0187
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0187_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0188
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0188
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0188_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0189
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.e0189
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP0.p0189_encode
