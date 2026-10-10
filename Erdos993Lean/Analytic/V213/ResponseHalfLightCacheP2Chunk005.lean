module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP2Chunk004

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 50: pow_succ.
def e0050 : Expr := Expr.pow e0002 2
def p0050 : Bi := exact_poly_nf_compact% (mul p0049 p0002)
theorem p0050_op : p0050 = mul p0049 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0050_encode : p0050 = Expr.encode e0050 [[0,1]] [[],[1]] := by
  rw [p0050_op]
  exact congrArg₂ mul p0049_encode p0002_encode

-- Source node 51: mul.
def e0051 : Expr := Expr.mul e0047 e0050
def p0051 : Bi := exact_poly_nf_compact% (mul p0047 p0050)
theorem p0051_op : p0051 = mul p0047 p0050 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0051_encode : p0051 = Expr.encode e0051 [[0,1]] [[],[1]] := by
  rw [p0051_op]
  exact congrArg₂ mul p0047_encode p0050_encode

-- Source node 52: mul.
def e0052 : Expr := Expr.mul e0051 e0001
def p0052 : Bi := exact_poly_nf_compact% (mul p0051 p0001)
theorem p0052_op : p0052 = mul p0051 p0001 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0052_encode : p0052 = Expr.encode e0052 [[0,1]] [[],[1]] := by
  rw [p0052_op]
  exact congrArg₂ mul p0051_encode p0001_encode

-- Source node 53: mul.
def e0053 : Expr := Expr.mul e0052 e0028
def p0053 : Bi := exact_poly_nf_compact% (mul p0052 p0028)
theorem p0053_op : p0053 = mul p0052 p0028 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0053_encode : p0053 = Expr.encode e0053 [[0,1]] [[],[1]] := by
  rw [p0053_op]
  exact congrArg₂ mul p0052_encode p0028_encode

-- Source node 54: neg.
def e0054 : Expr := Expr.neg e0053
def p0054 : Bi := exact_poly_nf_compact% (neg p0053)
theorem p0054_op : p0054 = neg p0053 := by decide +kernel
theorem p0054_encode : p0054 = Expr.encode e0054 [[0,1]] [[],[1]] := by
  rw [p0054_op]
  exact congrArg neg p0053_encode

-- Source node 55: add.
def e0055 : Expr := Expr.add e0041 e0054
def p0055 : Bi := exact_poly_nf_compact% (Bi.add p0041 p0054)
theorem p0055_op : p0055 = Bi.add p0041 p0054 := by decide +kernel
theorem p0055_encode : p0055 = Expr.encode e0055 [[0,1]] [[],[1]] := by
  rw [p0055_op]
  exact congrArg₂ Bi.add p0041_encode p0054_encode

-- Source node 56: constant.
def e0056 : Expr := Expr.constant (8 : ℚ)
def p0056 : Bi := exact_poly_nf_compact% (([[(8 : ℚ)]] : Bi))
theorem p0056_op : p0056 = ([[(8 : ℚ)]] : Bi) := by decide +kernel
theorem p0056_encode : p0056 = Expr.encode e0056 [[0,1]] [[],[1]] := by
  rw [p0056_op]
  rfl

-- Source node 57: mul.
def e0057 : Expr := Expr.mul e0056 e0000
def p0057 : Bi := exact_poly_nf_compact% (mul p0056 p0000)
theorem p0057_op : p0057 = mul p0056 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0057_encode : p0057 = Expr.encode e0057 [[0,1]] [[],[1]] := by
  rw [p0057_op]
  exact congrArg₂ mul p0056_encode p0000_encode

-- Source node 58: pow_succ.
def e0058 : Expr := Expr.pow e0002 3
def p0058 : Bi := exact_poly_nf_compact% (mul p0050 p0002)
theorem p0058_op : p0058 = mul p0050 p0002 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0058_encode : p0058 = Expr.encode e0058 [[0,1]] [[],[1]] := by
  rw [p0058_op]
  exact congrArg₂ mul p0050_encode p0002_encode

-- Source node 59: mul.
def e0059 : Expr := Expr.mul e0057 e0058
def p0059 : Bi := exact_poly_nf_compact% (mul p0057 p0058)
theorem p0059_op : p0059 = mul p0057 p0058 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0059_encode : p0059 = Expr.encode e0059 [[0,1]] [[],[1]] := by
  rw [p0059_op]
  exact congrArg₂ mul p0057_encode p0058_encode

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0050
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0050
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0050_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0051
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0051
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0051_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0052
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0052
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0052_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0053
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0053
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0053_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0054
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0054
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0054_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0055
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0055
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0055_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0056
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0056
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0056_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0057
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0057
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0057_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0058
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0058
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0058_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0059
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.e0059
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP2.p0059_encode
