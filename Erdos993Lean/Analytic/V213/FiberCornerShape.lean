module

public import Erdos993Lean.Analytic.V213.FiberWindowWeightData
public import Erdos993Lean.Analytic.V213.FiberInputRateShape

/-!
Canonical F14 logarithm/rate/corner formulas and F13 weighted
window formulas. Input rates and endpoints are the actual accepted
interfaces; window prices and time endpoints are actual F13 rows.
Source: Eq89.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberCornerFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def log (n : ℕ) (y : LowMeanIntegerShape) : LowMeanIntegerShape :=
  FiberRootLineFormula.logarithm n y

end FiberCornerFormula

def fiberCornerLogShape (id : FiberCornerLogIdentity) (gap : Bool) : LowMeanIntegerShape :=
  let r := fiberCornerLogById id
  let u := FiberCornerFormula.log r.n (.atom r.y)
  if gap then FiberCornerFormula.sub (.atom r.L) u else u

noncomputable def fiberCornerLogValue (id : FiberCornerLogIdentity) (gap : Bool) : ℝ :=
  let r := fiberCornerLogById id
  let u := fiberDyadicLog r.n (lowMeanFractionReal r.y)
  if gap then lowMeanFractionReal r.L - u else u

def fiberCornerRateShape (id : FiberCornerRateIdentity) : LowMeanIntegerShape :=
  let r := fiberCornerRateById id
  FiberCornerFormula.sub (.atom (fiberInputRouteById r.input).ell0)
    (.add (.atom r.base) (.mul (.atom r.slope) (.atom (fiberInputHiFraction r.input))))

noncomputable def fiberCornerRateValue (id : FiberCornerRateIdentity) : ℝ :=
  let r := fiberCornerRateById id
  lowMeanFractionReal (fiberInputRouteById r.input).ell0 -
    (lowMeanFractionReal r.base + lowMeanFractionReal r.slope * lowMeanFractionReal (fiberInputHiFraction r.input))

def fiberRateCornerShape (id : FiberRateCornerIdentity) : LowMeanIntegerShape :=
  let r := fiberRateCornerById id
  FiberCornerFormula.sub (.atom r.ell) (.mul (.atom r.L) (.atom r.ts))

noncomputable def fiberRateCornerValue (id : FiberRateCornerIdentity) : ℝ :=
  let r := fiberRateCornerById id
  lowMeanFractionReal r.ell - lowMeanFractionReal r.L * lowMeanFractionReal r.ts

def fiberWindowWeightShape (id : FiberWindowWeightIdentity) (gap : Bool) : LowMeanIntegerShape :=
  let r := fiberWindowWeightById id
  let w := fiberWindowById r.window
  let c := fiberWindowCornerById r.corner
  let u := FiberCornerFormula.log r.n (.div (.atom w.L_W) (.atom c.Z_W))
  if gap then FiberCornerFormula.sub
    (.mul (.atom c.mu_c) (FiberCornerFormula.sub (.atom c.ell_c) (.mul (.atom c.L_c) (.atom w.h)))) u
  else u

noncomputable def fiberWindowWeightValue (id : FiberWindowWeightIdentity) (gap : Bool) : ℝ :=
  let r := fiberWindowWeightById id
  let w := fiberWindowById r.window
  let c := fiberWindowCornerById r.corner
  let u := fiberDyadicLog r.n (lowMeanFractionReal w.L_W / lowMeanFractionReal c.Z_W)
  if gap then lowMeanFractionReal c.mu_c *
    (lowMeanFractionReal c.ell_c - lowMeanFractionReal c.L_c * lowMeanFractionReal w.h) - u
  else u

theorem fiber_corner_log_shape_real (id : FiberCornerLogIdentity) (gap : Bool) :
    lowMeanIntegerShapeReal (fiberCornerLogShape id gap) = fiberCornerLogValue id gap := by
  cases gap <;> simp only [fiberCornerLogShape,fiberCornerLogValue,Bool.false_eq_true,
    if_false,if_true,FiberCornerFormula.sub,FiberCornerFormula.log,lowMeanIntegerShapeReal,
    fiber_root_line_log_formula_real,sub_eq_add_neg]

theorem fiber_corner_rate_shape_real (id : FiberCornerRateIdentity) :
    lowMeanIntegerShapeReal (fiberCornerRateShape id) = fiberCornerRateValue id := by
  simp only [fiberCornerRateShape,fiberCornerRateValue,FiberCornerFormula.sub,
    lowMeanIntegerShapeReal,sub_eq_add_neg]

theorem fiber_rate_corner_shape_real (id : FiberRateCornerIdentity) :
    lowMeanIntegerShapeReal (fiberRateCornerShape id) = fiberRateCornerValue id := by
  simp only [fiberRateCornerShape,fiberRateCornerValue,FiberCornerFormula.sub,
    lowMeanIntegerShapeReal,sub_eq_add_neg]

theorem fiber_window_weight_shape_real (id : FiberWindowWeightIdentity) (gap : Bool) :
    lowMeanIntegerShapeReal (fiberWindowWeightShape id gap) = fiberWindowWeightValue id gap := by
  cases gap <;> simp only [fiberWindowWeightShape,fiberWindowWeightValue,Bool.false_eq_true,
    if_false,if_true,FiberCornerFormula.sub,FiberCornerFormula.log,lowMeanIntegerShapeReal,
    fiber_root_line_log_formula_real,sub_eq_add_neg]

end Erdos993Lean.Analytic.V213
