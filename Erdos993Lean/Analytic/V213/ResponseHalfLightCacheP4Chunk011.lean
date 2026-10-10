module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP4Chunk010

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 110: mul.
def e0110 : Expr := Expr.mul e0109 e0029
def p0110 : Bi := exact_poly_nf_compact% (mul p0109 p0029)
theorem p0110_op : p0110 = mul p0109 p0029 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0110_encode : p0110 = Expr.encode e0110 [[0,1]] [[],[1]] := by
  rw [p0110_op]
  exact congrArg₂ mul p0109_encode p0029_encode

-- Source node 111: mul.
def e0111 : Expr := Expr.mul e0110 e0028
def p0111 : Bi := exact_poly_nf_compact% (mul p0110 p0028)
theorem p0111_op : p0111 = mul p0110 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0111_encode : p0111 = Expr.encode e0111 [[0,1]] [[],[1]] := by
  rw [p0111_op]
  exact congrArg₂ mul p0110_encode p0028_encode

-- Source node 112: neg.
def e0112 : Expr := Expr.neg e0111
def p0112 : Bi := exact_poly_nf_compact% (neg p0111)
theorem p0112_op : p0112 = neg p0111 := by decide +kernel
theorem p0112_encode : p0112 = Expr.encode e0112 [[0,1]] [[],[1]] := by
  rw [p0112_op]
  exact congrArg neg p0111_encode

-- Source node 113: add.
def e0113 : Expr := Expr.add e0107 e0112
def p0113 : Bi := exact_poly_nf_compact% (Bi.add p0107 p0112)
theorem p0113_op : p0113 = Bi.add p0107 p0112 := by decide +kernel
theorem p0113_encode : p0113 = Expr.encode e0113 [[0,1]] [[],[1]] := by
  rw [p0113_op]
  exact congrArg₂ Bi.add p0107_encode p0112_encode

-- Source node 114: pow_zero.
def e0114 : Expr := Expr.pow e0029 0
def p0114 : Bi := exact_poly_nf_compact% (([[1]] : Bi))
theorem p0114_op : p0114 = ([[1]] : Bi) := by decide +kernel
theorem p0114_encode : p0114 = Expr.encode e0114 [[0,1]] [[],[1]] := by
  rw [p0114_op]
  rfl

-- Source node 115: pow_succ.
def e0115 : Expr := Expr.pow e0029 1
def p0115 : Bi := exact_poly_nf_compact% (mul p0114 p0029)
theorem p0115_op : p0115 = mul p0114 p0029 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0115_encode : p0115 = Expr.encode e0115 [[0,1]] [[],[1]] := by
  rw [p0115_op]
  exact congrArg₂ mul p0114_encode p0029_encode

-- Source node 116: pow_succ.
def e0116 : Expr := Expr.pow e0029 2
def p0116 : Bi := exact_poly_nf_compact% (mul p0115 p0029)
theorem p0116_op : p0116 = mul p0115 p0029 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0116_encode : p0116 = Expr.encode e0116 [[0,1]] [[],[1]] := by
  rw [p0116_op]
  exact congrArg₂ mul p0115_encode p0029_encode

-- Source node 117: mul.
def e0117 : Expr := Expr.mul e0023 e0116
def p0117 : Bi := exact_poly_nf_compact% (mul p0023 p0116)
theorem p0117_op : p0117 = mul p0023 p0116 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0117_encode : p0117 = Expr.encode e0117 [[0,1]] [[],[1]] := by
  rw [p0117_op]
  exact congrArg₂ mul p0023_encode p0116_encode

-- Source node 118: neg.
def e0118 : Expr := Expr.neg e0117
def p0118 : Bi := exact_poly_nf_compact% (neg p0117)
theorem p0118_op : p0118 = neg p0117 := by decide +kernel
theorem p0118_encode : p0118 = Expr.encode e0118 [[0,1]] [[],[1]] := by
  rw [p0118_op]
  exact congrArg neg p0117_encode

-- Source node 119: add.
def e0119 : Expr := Expr.add e0113 e0118
def p0119 : Bi := exact_poly_nf_compact% (Bi.add p0113 p0118)
theorem p0119_op : p0119 = Bi.add p0113 p0118 := by decide +kernel
theorem p0119_encode : p0119 = Expr.encode e0119 [[0,1]] [[],[1]] := by
  rw [p0119_op]
  exact congrArg₂ Bi.add p0113_encode p0118_encode

theorem source_upperRatioNum_026 : e0119 = upperRatioNum := by rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0110
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0110
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0110_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0111
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0111
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0111_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0112
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0112
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0112_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0113
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0113
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0113_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0114
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0114
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0114_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0115
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0115
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0115_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0116
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0116
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0116_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0117
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0117
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0117_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0118
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0118
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0118_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0119
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.e0119
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.p0119_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_upperRatioNum_026
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP4.source_upperRatioNum_026
