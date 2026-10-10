module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP1Chunk012

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 130: mul.
def e0130 : Expr := Expr.mul e0061 e0023
def p0130 : Bi := exact_poly_nf_compact% (mul p0061 p0023)
theorem p0130_op : p0130 = mul p0061 p0023 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0130_encode : p0130 = Expr.encode e0130 [[0,1]] [[],[1]] := by
  rw [p0130_op]
  exact congrArg₂ mul p0061_encode p0023_encode

-- Source node 131: mul.
def e0131 : Expr := Expr.mul e0130 e0035
def p0131 : Bi := exact_poly_nf_compact% (mul p0130 p0035)
theorem p0131_op : p0131 = mul p0130 p0035 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0131_encode : p0131 = Expr.encode e0131 [[0,1]] [[],[1]] := by
  rw [p0131_op]
  exact congrArg₂ mul p0130_encode p0035_encode

-- Source node 132: mul.
def e0132 : Expr := Expr.mul e0131 e0006
def p0132 : Bi := exact_poly_nf_compact% (mul p0131 p0006)
theorem p0132_op : p0132 = mul p0131 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0132_encode : p0132 = Expr.encode e0132 [[0,1]] [[],[1]] := by
  rw [p0132_op]
  exact congrArg₂ mul p0131_encode p0006_encode

-- Source node 133: mul.
def e0133 : Expr := Expr.mul e0132 e0004
def p0133 : Bi := exact_poly_nf_compact% (mul p0132 p0004)
theorem p0133_op : p0133 = mul p0132 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0133_encode : p0133 = Expr.encode e0133 [[0,1]] [[],[1]] := by
  rw [p0133_op]
  exact congrArg₂ mul p0132_encode p0004_encode

-- Source node 134: add.
def e0134 : Expr := Expr.add e0084 e0133
def p0134 : Bi := exact_poly_nf_compact% (Bi.add p0084 p0133)
theorem p0134_op : p0134 = Bi.add p0084 p0133 := by decide +kernel
theorem p0134_encode : p0134 = Expr.encode e0134 [[0,1]] [[],[1]] := by
  rw [p0134_op]
  exact congrArg₂ Bi.add p0084_encode p0133_encode

-- Source node 135: mul.
def e0135 : Expr := Expr.mul e0023 e0063
def p0135 : Bi := exact_poly_nf_compact% (mul p0023 p0063)
theorem p0135_op : p0135 = mul p0023 p0063 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0135_encode : p0135 = Expr.encode e0135 [[0,1]] [[],[1]] := by
  rw [p0135_op]
  exact congrArg₂ mul p0023_encode p0063_encode

-- Source node 136: mul.
def e0136 : Expr := Expr.mul e0135 e0006
def p0136 : Bi := exact_poly_nf_compact% (mul p0135 p0006)
theorem p0136_op : p0136 = mul p0135 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0136_encode : p0136 = Expr.encode e0136 [[0,1]] [[],[1]] := by
  rw [p0136_op]
  exact congrArg₂ mul p0135_encode p0006_encode

-- Source node 137: mul.
def e0137 : Expr := Expr.mul e0136 e0006
def p0137 : Bi := exact_poly_nf_compact% (mul p0136 p0006)
theorem p0137_op : p0137 = mul p0136 p0006 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0137_encode : p0137 = Expr.encode e0137 [[0,1]] [[],[1]] := by
  rw [p0137_op]
  exact congrArg₂ mul p0136_encode p0006_encode

-- Source node 138: mul.
def e0138 : Expr := Expr.mul e0137 e0019
def p0138 : Bi := exact_poly_nf_compact% (mul p0137 p0019)
theorem p0138_op : p0138 = mul p0137 p0019 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0138_encode : p0138 = Expr.encode e0138 [[0,1]] [[],[1]] := by
  rw [p0138_op]
  exact congrArg₂ mul p0137_encode p0019_encode

-- Source node 139: mul.
def e0139 : Expr := Expr.mul e0138 e0105
def p0139 : Bi := exact_poly_nf_compact% (mul p0138 p0105)
theorem p0139_op : p0139 = mul p0138 p0105 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0139_encode : p0139 = Expr.encode e0139 [[0,1]] [[],[1]] := by
  rw [p0139_op]
  exact congrArg₂ mul p0138_encode p0105_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0130
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0130
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0130_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0131
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0131
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0131_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0132
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0132
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0132_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0133
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0133
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0133_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0134
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0134
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0134_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0135
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0135
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0135_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0136
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0136
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0136_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0137
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0137
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0137_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0138
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0138
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0138_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0139
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0139
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0139_encode
