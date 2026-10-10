module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP1Chunk011

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 120: pow_succ.
def e0120 : Expr := Expr.pow e0029 1
def p0120 : Bi := exact_poly_nf_compact% (mul p0119 p0029)
theorem p0120_op : p0120 = mul p0119 p0029 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0120_encode : p0120 = Expr.encode e0120 [[0,1]] [[],[1]] := by
  rw [p0120_op]
  exact congrArg₂ mul p0119_encode p0029_encode

-- Source node 121: pow_succ.
def e0121 : Expr := Expr.pow e0029 2
def p0121 : Bi := exact_poly_nf_compact% (mul p0120 p0029)
theorem p0121_op : p0121 = mul p0120 p0029 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0121_encode : p0121 = Expr.encode e0121 [[0,1]] [[],[1]] := by
  rw [p0121_op]
  exact congrArg₂ mul p0120_encode p0029_encode

-- Source node 122: mul.
def e0122 : Expr := Expr.mul e0023 e0121
def p0122 : Bi := exact_poly_nf_compact% (mul p0023 p0121)
theorem p0122_op : p0122 = mul p0023 p0121 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0122_encode : p0122 = Expr.encode e0122 [[0,1]] [[],[1]] := by
  rw [p0122_op]
  exact congrArg₂ mul p0023_encode p0121_encode

-- Source node 123: neg.
def e0123 : Expr := Expr.neg e0122
def p0123 : Bi := exact_poly_nf_compact% (neg p0122)
theorem p0123_op : p0123 = neg p0122 := by decide +kernel
theorem p0123_encode : p0123 = Expr.encode e0123 [[0,1]] [[],[1]] := by
  rw [p0123_op]
  exact congrArg neg p0122_encode

-- Source node 124: add.
def e0124 : Expr := Expr.add e0118 e0123
def p0124 : Bi := exact_poly_nf_compact% (Bi.add p0118 p0123)
theorem p0124_op : p0124 = Bi.add p0118 p0123 := by decide +kernel
theorem p0124_encode : p0124 = Expr.encode e0124 [[0,1]] [[],[1]] := by
  rw [p0124_op]
  exact congrArg₂ Bi.add p0118_encode p0123_encode

theorem source_upperRatioNum_026 : e0124 = upperRatioNum := by rfl

-- Source node 125: constant.
def e0125 : Expr := Expr.constant (16 : ℚ)
def p0125 : Bi := exact_poly_nf_compact% (([[(16 : ℚ)]] : Bi))
theorem p0125_op : p0125 = ([[(16 : ℚ)]] : Bi) := by decide +kernel
theorem p0125_encode : p0125 = Expr.encode e0125 [[0,1]] [[],[1]] := by
  rw [p0125_op]
  rfl

-- Source node 126: mul.
def e0126 : Expr := Expr.mul e0125 e0000
def p0126 : Bi := exact_poly_nf_compact% (mul p0125 p0000)
theorem p0126_op : p0126 = mul p0125 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0126_encode : p0126 = Expr.encode e0126 [[0,1]] [[],[1]] := by
  rw [p0126_op]
  exact congrArg₂ mul p0125_encode p0000_encode

-- Source node 127: mul.
def e0127 : Expr := Expr.mul e0126 e0063
def p0127 : Bi := exact_poly_nf_compact% (mul p0126 p0063)
theorem p0127_op : p0127 = mul p0126 p0063 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0127_encode : p0127 = Expr.encode e0127 [[0,1]] [[],[1]] := by
  rw [p0127_op]
  exact congrArg₂ mul p0126_encode p0063_encode

-- Source node 128: mul.
def e0128 : Expr := Expr.mul e0127 e0006
def p0128 : Bi := exact_poly_nf_compact% (mul p0127 p0006)
theorem p0128_op : p0128 = mul p0127 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0128_encode : p0128 = Expr.encode e0128 [[0,1]] [[],[1]] := by
  rw [p0128_op]
  exact congrArg₂ mul p0127_encode p0006_encode

-- Source node 129: add.
def e0129 : Expr := Expr.add e0084 e0128
def p0129 : Bi := exact_poly_nf_compact% (Bi.add p0084 p0128)
theorem p0129_op : p0129 = Bi.add p0084 p0128 := by decide +kernel
theorem p0129_encode : p0129 = Expr.encode e0129 [[0,1]] [[],[1]] := by
  rw [p0129_op]
  exact congrArg₂ Bi.add p0084_encode p0128_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0120
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0120
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0120_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0121
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0121
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0121_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0122
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0122
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0122_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0123
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0123
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0123_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0124
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0124
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0124_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_upperRatioNum_026
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_upperRatioNum_026
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0125
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0125
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0125_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0126
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0126
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0126_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0127
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0127
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0127_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0128
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0128
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0128_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0129
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0129
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0129_encode
