module

public import Erdos993Lean.Analytic.V213.ResponseHalfLightCacheP1Chunk000

/-! Generated cache: expression nodes with their polynomials and encoding identities. -/

@[expose] public section

namespace Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

open Erdos993Lean.BCFG
open Erdos993Lean.Analytic.V213.ZeroTiltLaplace.FinitePolynomial

-- Source node 10: mul.
def e0010 : Expr := Expr.mul e0000 e0004
def p0010 : Bi := exact_poly_nf_compact% (mul p0000 p0004)
theorem p0010_op : p0010 = mul p0000 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0010_encode : p0010 = Expr.encode e0010 [[0,1]] [[],[1]] := by
  rw [p0010_op]
  exact congrArg₂ mul p0000_encode p0004_encode

-- Source node 11: neg.
def e0011 : Expr := Expr.neg e0010
def p0011 : Bi := exact_poly_nf_compact% (neg p0010)
theorem p0011_op : p0011 = neg p0010 := by decide +kernel
theorem p0011_encode : p0011 = Expr.encode e0011 [[0,1]] [[],[1]] := by
  rw [p0011_op]
  exact congrArg neg p0010_encode

-- Source node 12: add.
def e0012 : Expr := Expr.add e0009 e0011
def p0012 : Bi := exact_poly_nf_compact% (Bi.add p0009 p0011)
theorem p0012_op : p0012 = Bi.add p0009 p0011 := by decide +kernel
theorem p0012_encode : p0012 = Expr.encode e0012 [[0,1]] [[],[1]] := by
  rw [p0012_op]
  exact congrArg₂ Bi.add p0009_encode p0011_encode

theorem source_factorD_004 : e0012 = factorD := by rfl

-- Source node 13: mul.
def e0013 : Expr := Expr.mul e0003 e0000
def p0013 : Bi := exact_poly_nf_compact% (mul p0003 p0000)
theorem p0013_op : p0013 = mul p0003 p0000 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0013_encode : p0013 = Expr.encode e0013 [[0,1]] [[],[1]] := by
  rw [p0013_op]
  exact congrArg₂ mul p0003_encode p0000_encode

-- Source node 14: add.
def e0014 : Expr := Expr.add e0003 e0013
def p0014 : Bi := exact_poly_nf_compact% (Bi.add p0003 p0013)
theorem p0014_op : p0014 = Bi.add p0003 p0013 := by decide +kernel
theorem p0014_encode : p0014 = Expr.encode e0014 [[0,1]] [[],[1]] := by
  rw [p0014_op]
  exact congrArg₂ Bi.add p0003_encode p0013_encode

-- Source node 15: neg.
def e0015 : Expr := Expr.neg e0001
def p0015 : Bi := exact_poly_nf_compact% (neg p0001)
theorem p0015_op : p0015 = neg p0001 := by decide +kernel
theorem p0015_encode : p0015 = Expr.encode e0015 [[0,1]] [[],[1]] := by
  rw [p0015_op]
  exact congrArg neg p0001_encode

-- Source node 16: add.
def e0016 : Expr := Expr.add e0000 e0015
def p0016 : Bi := exact_poly_nf_compact% (Bi.add p0000 p0015)
theorem p0016_op : p0016 = Bi.add p0000 p0015 := by decide +kernel
theorem p0016_encode : p0016 = Expr.encode e0016 [[0,1]] [[],[1]] := by
  rw [p0016_op]
  exact congrArg₂ Bi.add p0000_encode p0015_encode

-- Source node 17: mul.
def e0017 : Expr := Expr.mul e0016 e0004
def p0017 : Bi := exact_poly_nf_compact% (mul p0016 p0004)
theorem p0017_op : p0017 = mul p0016 p0004 :=
  Erdos993Lean.Analytic.V213.HalfLightFast.IntPoly.mul_of_mulCheck (by decide +kernel)
theorem p0017_encode : p0017 = Expr.encode e0017 [[0,1]] [[],[1]] := by
  rw [p0017_op]
  exact congrArg₂ mul p0016_encode p0004_encode

-- Source node 18: neg.
def e0018 : Expr := Expr.neg e0017
def p0018 : Bi := exact_poly_nf_compact% (neg p0017)
theorem p0018_op : p0018 = neg p0017 := by decide +kernel
theorem p0018_encode : p0018 = Expr.encode e0018 [[0,1]] [[],[1]] := by
  rw [p0018_op]
  exact congrArg neg p0017_encode

-- Source node 19: add.
def e0019 : Expr := Expr.add e0014 e0018
def p0019 : Bi := exact_poly_nf_compact% (Bi.add p0014 p0018)
theorem p0019_op : p0019 = Bi.add p0014 p0018 := by decide +kernel
theorem p0019_encode : p0019 = Expr.encode e0019 [[0,1]] [[],[1]] := by
  rw [p0019_op]
  exact congrArg₂ Bi.add p0014_encode p0018_encode

theorem source_factorE_005 : e0019 = factorE := by rfl

end Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1

#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0010
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0010
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0010_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0011
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0011
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0011_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0012
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0012
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0012_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_factorD_004
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_factorD_004
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0013
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0013
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0013_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0014
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0014
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0014_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0015
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0015
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0015_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0016
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0016
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0016_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0017
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0017
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0017_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0018
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0018
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0018_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0019
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.e0019
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019_op
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019_op
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019_encode
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.p0019_encode
#check Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_factorE_005
#print axioms Erdos993Lean.Analytic.V213.VarianceResponse.ParentRows.HalfLightPolys.StagedP1.source_factorE_005
