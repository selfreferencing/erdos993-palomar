module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP7Chunk009

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 100: neg.
def e0100 : Expr := Expr.neg e0099
def p0100 : Bi := exact_poly_nf_compact% (neg p0099)
theorem p0100_op : p0100 = neg p0099 := by decide +kernel
theorem p0100_encode : p0100 = Expr.encode e0100 [[0,1]] [[],[1]] := by
  rw [p0100_op]
  exact congrArg neg p0099_encode

-- Source node 101: add.
def e0101 : Expr := Expr.add e0095 e0100
def p0101 : Bi := exact_poly_nf_compact% (Bi.add p0095 p0100)
theorem p0101_op : p0101 = Bi.add p0095 p0100 := by decide +kernel
theorem p0101_encode : p0101 = Expr.encode e0101 [[0,1]] [[],[1]] := by
  rw [p0101_op]
  exact congrArg₂ Bi.add p0095_encode p0100_encode

-- Source node 102: mul.
def e0102 : Expr := Expr.mul e0003 e0101
def p0102 : Bi := exact_poly_nf_compact% (mul p0003 p0101)
theorem p0102_op : p0102 = mul p0003 p0101 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0102_encode : p0102 = Expr.encode e0102 [[0,1]] [[],[1]] := by
  rw [p0102_op]
  exact congrArg₂ mul p0003_encode p0101_encode

-- Source node 103: pow_zero.
def e0103 : Expr := Expr.pow e0028 0
def p0103 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0103_op : p0103 = ([[1]] : Bi) := by decide +kernel
theorem p0103_encode : p0103 = Expr.encode e0103 [[0,1]] [[],[1]] := by
  rw [p0103_op]
  rfl

-- Source node 104: pow_succ.
def e0104 : Expr := Expr.pow e0028 1
def p0104 : Bi := exact_poly_nf_compact% (mul p0103 p0028)
theorem p0104_op : p0104 = mul p0103 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0104_encode : p0104 = Expr.encode e0104 [[0,1]] [[],[1]] := by
  rw [p0104_op]
  exact congrArg₂ mul p0103_encode p0028_encode

-- Source node 105: pow_succ.
def e0105 : Expr := Expr.pow e0028 2
def p0105 : Bi := exact_poly_nf_compact% (mul p0104 p0028)
theorem p0105_op : p0105 = mul p0104 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0105_encode : p0105 = Expr.encode e0105 [[0,1]] [[],[1]] := by
  rw [p0105_op]
  exact congrArg₂ mul p0104_encode p0028_encode

-- Source node 106: mul.
def e0106 : Expr := Expr.mul e0102 e0105
def p0106 : Bi := exact_poly_nf_compact% (mul p0102 p0105)
theorem p0106_op : p0106 = mul p0102 p0105 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0106_encode : p0106 = Expr.encode e0106 [[0,1]] [[],[1]] := by
  rw [p0106_op]
  exact congrArg₂ mul p0102_encode p0105_encode

-- Source node 107: mul.
def e0107 : Expr := Expr.mul e0023 e0012
def p0107 : Bi := exact_poly_nf_compact% (mul p0023 p0012)
theorem p0107_op : p0107 = mul p0023 p0012 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0107_encode : p0107 = Expr.encode e0107 [[0,1]] [[],[1]] := by
  rw [p0107_op]
  exact congrArg₂ mul p0023_encode p0012_encode

-- Source node 108: mul.
def e0108 : Expr := Expr.mul e0107 e0004
def p0108 : Bi := exact_poly_nf_compact% (mul p0107 p0004)
theorem p0108_op : p0108 = mul p0107 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0108_encode : p0108 = Expr.encode e0108 [[0,1]] [[],[1]] := by
  rw [p0108_op]
  exact congrArg₂ mul p0107_encode p0004_encode

-- Source node 109: neg.
def e0109 : Expr := Expr.neg e0108
def p0109 : Bi := exact_poly_nf_compact% (neg p0108)
theorem p0109_op : p0109 = neg p0108 := by decide +kernel
theorem p0109_encode : p0109 = Expr.encode e0109 [[0,1]] [[],[1]] := by
  rw [p0109_op]
  exact congrArg neg p0108_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0100
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0100
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0100_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0101
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0101
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0101_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0102
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0102
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0102_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0103
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0103
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0103_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0104
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0104
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0104_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0105
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0105
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0105_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0106
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0106
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0106_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0107
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0107
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0107_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0108
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0108
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0108_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0109
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.e0109
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP7.p0109_encode
