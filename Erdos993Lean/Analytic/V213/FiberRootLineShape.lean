module

public import Erdos993Lean.Analytic.V213.FiberRootLineData
public import Erdos993Lean.Analytic.V213.FiberDyadicLog

/-!
Complete F09 formula shapes and real interpretations. Eq89 retains
the printed dyadic exponent, argument, all series coefficients and all
root-line leaves. No check of an unrelated positive result can pass this
shape comparison.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberRootLineFormula

def sub (a b : LowMeanIntegerShape) : LowMeanIntegerShape := .add a (.neg b)

def logarithm (n : ℕ) (y : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let w := .div y (.pow (.atom (2,1)) n)
  let z := .div (sub w (.atom (1,1))) (.add w (.atom (1,1)))
  .add (.div (.mul (.atom (1733,1)) (.atom (n,1))) (.atom (2500,1)))
    (.add (.mul (.atom (2,1))
      (.add (.add z (.div (.pow z 3) (.atom (3,1)))) (.div (.pow z 5) (.atom (5,1)))))
      (.div (.mul (.atom (2,1)) (.pow z 7))
        (.mul (.atom (7,1)) (sub (.atom (1,1)) (.pow z 2)))))

end FiberRootLineFormula

def fiberRootLineArgumentShape (id : FiberRootLineIdentity) : LowMeanIntegerShape :=
  let r := fiberRootLineById id
  .mul (.pow (FiberRootLineFormula.sub (.atom (1,1)) (.atom r.v)) 2)
    (.pow (.div (.atom r.beta) (.atom r.k)) 5)

def fiberRootLineShape (id : FiberRootLineIdentity) (role : FiberRootLineRole) : LowMeanIntegerShape :=
  let r := fiberRootLineById id
  let L := FiberRootLineFormula.logarithm r.n (fiberRootLineArgumentShape id)
  match role with
  | .logarithm => L
  | .rootGap => FiberRootLineFormula.sub (.mul (.atom (2,1)) (.atom r.v)) L
  | .convexityGap => FiberRootLineFormula.sub
      (.mul (.mul (.atom (4,1)) (.atom r.beta))
        (FiberRootLineFormula.sub (.atom r.alpha) (.atom (1,1))))
      (.mul (.atom (15,1)) (.pow (.add (FiberRootLineFormula.sub (.atom (1,1)) (.atom r.alpha))
        (.mul (.atom r.beta) (.atom r.hi))) 3))

noncomputable def fiberRootLineArgument (id : FiberRootLineIdentity) : ℝ :=
  (1 - lowMeanFractionReal (fiberRootLineById id).v) ^ 2 *
    (lowMeanFractionReal (fiberRootLineById id).beta / lowMeanFractionReal (fiberRootLineById id).k) ^ 5

noncomputable def fiberRootLineValue (id : FiberRootLineIdentity) (role : FiberRootLineRole) : ℝ :=
  let r := fiberRootLineById id
  match role with
  | .logarithm => fiberDyadicLog r.n (fiberRootLineArgument id)
  | .rootGap => 2 * lowMeanFractionReal r.v - fiberDyadicLog r.n (fiberRootLineArgument id)
  | .convexityGap => 4 * lowMeanFractionReal r.beta * (lowMeanFractionReal r.alpha - 1) -
      15 * (1 - lowMeanFractionReal r.alpha + lowMeanFractionReal r.beta * lowMeanFractionReal r.hi) ^ 3

theorem fiber_root_line_log_formula_real (n : ℕ) (y : LowMeanIntegerShape) :
    lowMeanIntegerShapeReal (FiberRootLineFormula.logarithm n y) =
      fiberDyadicLog n (lowMeanIntegerShapeReal y) := by
  simp only [FiberRootLineFormula.logarithm,FiberRootLineFormula.sub,lowMeanIntegerShapeReal,
    lowMeanFractionReal,Int.cast_ofNat,Int.cast_natCast,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,
    div_one,fiberDyadicLog,FreeCountVariance.Envelopes.seriesT,FreeCountVariance.Envelopes.seriesS]
  norm_num
  ring

theorem fiber_root_line_argument_shape_real (id : FiberRootLineIdentity) :
    lowMeanIntegerShapeReal (fiberRootLineArgumentShape id) = fiberRootLineArgument id := by
  simp only [fiberRootLineArgumentShape,FiberRootLineFormula.sub,lowMeanIntegerShapeReal,
    fiberRootLineArgument,lowMeanFractionReal,Int.cast_one,Nat.cast_one,div_one]
  ring

theorem fiber_root_line_shape_real (id : FiberRootLineIdentity) (role : FiberRootLineRole) :
    lowMeanIntegerShapeReal (fiberRootLineShape id role) = fiberRootLineValue id role := by
  cases role <;> simp only [fiberRootLineShape,fiberRootLineValue,FiberRootLineFormula.sub,
    lowMeanIntegerShapeReal,fiber_root_line_log_formula_real,fiber_root_line_argument_shape_real,
    lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,div_one] <;> ring

end Erdos993Lean.Analytic.V213
