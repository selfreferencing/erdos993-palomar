module

public import Erdos993Lean.Analytic.V213.FiberWeightedChordData
public import Erdos993Lean.Analytic.V213.FiberProfileChordBounds

/-!
Complete canonical F12 formula binding. Both Eq98 routes retain
the actual F10 chord endpoints and the printed F11 weight parameters.
The real interpretation is the Eq89 enclosure of the actual weighted
chord argument.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberWeightedChordFormula

def sub (a b : LowMeanIntegerShape) : LowMeanIntegerShape := .add a (.neg b)

def parameters (id : FiberWeightedChordIdentity) :
    LowMeanIntegerShape × LowMeanIntegerShape × LowMeanIntegerShape × LowMeanIntegerShape × LowMeanIntegerShape :=
  let r := fiberWeightedChordById id
  let w := fiberWeightById r.weight
  let c := fiberProfileChordById r.chord
  let l := fiberProfileControlById c.left
  let h := fiberProfileControlById c.right
  let s := .div (sub (.atom l.z) (.atom h.z)) (sub (.atom h.t) (.atom l.t))
  let d := .add (.atom l.t) (.div (.atom l.z) s)
  let k := .mul (.atom w.mu_w) (.atom w.L_w)
  let v := .mul (.atom w.mu_w) (.atom w.ell_w)
  let y := if r.endpointRoute then .div (.atom h.z) (.atom w.eta_w)
    else .div s (.mul k (.atom w.eta_w))
  (s,d,k,v,y)

end FiberWeightedChordFormula

def fiberWeightedChordShape (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) : LowMeanIntegerShape :=
  let r := fiberWeightedChordById id
  let c := fiberProfileChordById r.chord
  let p := FiberWeightedChordFormula.parameters id
  let U := FiberRootLineFormula.logarithm r.n p.2.2.2.2
  match role with
  | .logarithm => U
  | .gap => if r.endpointRoute then FiberWeightedChordFormula.sub
      (FiberWeightedChordFormula.sub p.2.2.2.1 (.mul p.2.2.1 (.atom (fiberProfileControlById c.right).t))) U
    else FiberWeightedChordFormula.sub
      (FiberWeightedChordFormula.sub (.add p.2.2.2.1 (.atom (1,1))) (.mul p.2.2.1 p.2.1)) U

noncomputable def fiberWeightedChordParameters (id : FiberWeightedChordIdentity) :
    ℝ × ℝ × ℝ × ℝ × ℝ :=
  let r := fiberWeightedChordById id
  let w := fiberWeightById r.weight
  let c := fiberProfileChordById r.chord
  let l := fiberProfileControlById c.left
  let h := fiberProfileControlById c.right
  let s := (lowMeanFractionReal l.z - lowMeanFractionReal h.z) /
    (lowMeanFractionReal h.t - lowMeanFractionReal l.t)
  let d := lowMeanFractionReal l.t + lowMeanFractionReal l.z / s
  let k := lowMeanFractionReal w.mu_w * lowMeanFractionReal w.L_w
  let v := lowMeanFractionReal w.mu_w * lowMeanFractionReal w.ell_w
  let y := if r.endpointRoute then lowMeanFractionReal h.z / lowMeanFractionReal w.eta_w
    else s / (k * lowMeanFractionReal w.eta_w)
  (s,d,k,v,y)

noncomputable def fiberWeightedChordValue (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) : ℝ :=
  let r := fiberWeightedChordById id
  let p := fiberWeightedChordParameters id
  let U := fiberDyadicLog r.n p.2.2.2.2
  match role with
  | .logarithm => U
  | .gap => if r.endpointRoute then p.2.2.2.1 -
      p.2.2.1 * lowMeanFractionReal (fiberProfileControlById
        (fiberProfileChordById r.chord).right).t - U
    else p.2.2.2.1 + 1 - p.2.2.1 * p.2.1 - U

theorem fiber_weighted_chord_parameters_real (id : FiberWeightedChordIdentity) :
    lowMeanIntegerShapeReal (FiberWeightedChordFormula.parameters id).1 = (fiberWeightedChordParameters id).1 ∧
    lowMeanIntegerShapeReal (FiberWeightedChordFormula.parameters id).2.1 = (fiberWeightedChordParameters id).2.1 ∧
    lowMeanIntegerShapeReal (FiberWeightedChordFormula.parameters id).2.2.1 = (fiberWeightedChordParameters id).2.2.1 ∧
    lowMeanIntegerShapeReal (FiberWeightedChordFormula.parameters id).2.2.2.1 = (fiberWeightedChordParameters id).2.2.2.1 ∧
    lowMeanIntegerShapeReal (FiberWeightedChordFormula.parameters id).2.2.2.2 = (fiberWeightedChordParameters id).2.2.2.2 := by
  simp only [FiberWeightedChordFormula.parameters,FiberWeightedChordFormula.sub,
    fiberWeightedChordParameters,lowMeanIntegerShapeReal]
  split <;> simp [lowMeanIntegerShapeReal,sub_eq_add_neg]

theorem fiber_weighted_chord_shape_real (id : FiberWeightedChordIdentity) (role : FiberWeightedChordRole) :
    lowMeanIntegerShapeReal (fiberWeightedChordShape id role) = fiberWeightedChordValue id role := by
  have hp := fiber_weighted_chord_parameters_real id
  cases role <;> simp only [fiberWeightedChordShape,fiberWeightedChordValue,
    FiberWeightedChordFormula.sub,lowMeanIntegerShapeReal,fiber_root_line_log_formula_real,
    hp.1,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,
    lowMeanFractionReal,Int.cast_one,Nat.cast_one,div_one]
  split <;> simp only [FiberWeightedChordFormula.sub,lowMeanIntegerShapeReal,
    fiber_root_line_log_formula_real,hp.2.1,hp.2.2.1,hp.2.2.2.1,hp.2.2.2.2,
    lowMeanFractionReal,Int.cast_one,Nat.cast_one,div_one] <;> ring

theorem fiber_weighted_chord_stored_parameters (id : FiberWeightedChordIdentity) :
    fiberWeightedChordParameters id =
      (lowMeanFractionReal (fiberWeightedChordById id).s,
       lowMeanFractionReal (fiberWeightedChordById id).d,
       lowMeanFractionReal (fiberWeightedChordById id).k,
       lowMeanFractionReal (fiberWeightedChordById id).v,
       lowMeanFractionReal (fiberWeightedChordById id).y) := by
  cases id <;> norm_num [fiberWeightedChordParameters,fiberWeightedChordById,
    fiberWeightById,fiberProfileChordById,fiberProfileControlById,lowMeanFractionReal]

end Erdos993Lean.Analytic.V213
