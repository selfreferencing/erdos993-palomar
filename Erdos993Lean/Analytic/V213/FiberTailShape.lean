module

public import Erdos993Lean.Analytic.V213.FiberTailData
public import Erdos993Lean.Analytic.V213.FiberCornerShape

/-!
Complete canonical Eq104 trees, including the actual F11
weight leaves in group x_a and the explicit ordinary geometric branch.
Branch/parameter/domain checks and all-real price consumers are separate.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberTailFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def a (id : FiberTailIdentity) : LowMeanIntegerShape :=
  let r := fiberTailById id
  let base := .mul (.atom (51,200)) (.atom r.C)
  .mul base (match r.weight with
    | some _ => .pow (.atom (27,40)) 7
    | none => if r.geometricOne then .atom (1,1)
      else .pow (.mul (.atom (27,40)) (.atom (r.h_i.getD (1,1)))) 7)

def b (id : FiberTailIdentity) : LowMeanIntegerShape :=
  .mul (.atom (81,5000)) (.atom (fiberTailById id).C)

def xa (id : FiberTailIdentity) : LowMeanIntegerShape :=
  let r := fiberTailById id
  match r.weight with
    | some wid => sub (.mul (.atom r.mu) (.atom (fiberWeightById wid).ell_w))
      (.mul (.atom (7,1)) (.atom (fiberWeightById wid).L_w))
    | none => .mul (.atom r.mu) (.atom r.ell)

def xs (id : FiberTailIdentity) : LowMeanIntegerShape :=
  .mul (.atom (fiberTailById id).m) (.atom (fiberTailById id).d)

def ya (id : FiberTailIdentity) : LowMeanIntegerShape :=
  let r := fiberTailById id
  .div (.mul (.pow (a id) 2) (.pow (.atom r.mu) 3)) (.pow (.atom r.Z_a) 2)

def ys (id : FiberTailIdentity) : LowMeanIntegerShape :=
  let r := fiberTailById id
  .div (.mul (.pow (b id) 2) (.pow (.atom r.m) 3)) (.pow (.atom r.Z_small) 2)

end FiberTailFormula

noncomputable def fiberTailA (id : FiberTailIdentity) : ℝ :=
  let r := fiberTailById id
  (51/200 : ℝ)*lowMeanFractionReal r.C*(match r.weight with
    | some _ => (27/40 : ℝ)^7
    | none => if r.geometricOne then 1
      else ((27/40 : ℝ)*lowMeanFractionReal (r.h_i.getD (1,1)))^7)

noncomputable def fiberTailB (id : FiberTailIdentity) : ℝ :=
  (81/5000 : ℝ)*lowMeanFractionReal (fiberTailById id).C

noncomputable def fiberTailXA (id : FiberTailIdentity) : ℝ :=
  let r := fiberTailById id
  match r.weight with
    | some wid => lowMeanFractionReal r.mu*lowMeanFractionReal (fiberWeightById wid).ell_w-
      7*lowMeanFractionReal (fiberWeightById wid).L_w
    | none => lowMeanFractionReal r.mu*lowMeanFractionReal r.ell

noncomputable def fiberTailXS (id : FiberTailIdentity) : ℝ :=
  lowMeanFractionReal (fiberTailById id).m*lowMeanFractionReal (fiberTailById id).d

noncomputable def fiberTailYA (id : FiberTailIdentity) : ℝ :=
  let r := fiberTailById id
  (fiberTailA id)^2*(lowMeanFractionReal r.mu)^3/(lowMeanFractionReal r.Z_a)^2

noncomputable def fiberTailYS (id : FiberTailIdentity) : ℝ :=
  let r := fiberTailById id
  (fiberTailB id)^2*(lowMeanFractionReal r.m)^3/(lowMeanFractionReal r.Z_small)^2

def fiberTailShape (id : FiberTailIdentity) (role : FiberTailRole) : LowMeanIntegerShape :=
  let r := fiberTailById id
  let ua := FiberRootLineFormula.logarithm r.n_a (FiberTailFormula.ya id)
  let us := FiberRootLineFormula.logarithm r.n_s (FiberTailFormula.ys id)
  match role with
    | .smallLog => ua
    | .smallGap => FiberTailFormula.sub (.mul (.atom (2,1)) (FiberTailFormula.xa id)) ua
    | .largeLog => us
    | .largeGap => FiberTailFormula.sub (.mul (.atom (2,1)) (FiberTailFormula.xs id)) us

noncomputable def fiberTailValue (id : FiberTailIdentity) (role : FiberTailRole) : ℝ :=
  let r := fiberTailById id
  let ua := fiberDyadicLog r.n_a (fiberTailYA id)
  let us := fiberDyadicLog r.n_s (fiberTailYS id)
  match role with
    | .smallLog => ua
    | .smallGap => 2*fiberTailXA id-ua
    | .largeLog => us
    | .largeGap => 2*fiberTailXS id-us

theorem fiber_tail_shape_real (id : FiberTailIdentity) (role : FiberTailRole) :
    lowMeanIntegerShapeReal (fiberTailShape id role) = fiberTailValue id role := by
  cases role <;> cases hw : (fiberTailById id).weight <;>
    cases hg : (fiberTailById id).geometricOne <;>
    simp only [fiberTailShape,fiberTailValue,FiberTailFormula.ya,FiberTailFormula.ys,
      FiberTailFormula.a,FiberTailFormula.b,FiberTailFormula.xa,FiberTailFormula.xs,
      FiberTailFormula.sub,fiberTailYA,fiberTailYS,fiberTailA,fiberTailB,fiberTailXA,fiberTailXS,
      hw,hg,Bool.false_eq_true,if_false,if_true,lowMeanIntegerShapeReal,
      fiber_root_line_log_formula_real,lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,
      div_one,one_div,sub_eq_add_neg]

end Erdos993Lean.Analytic.V213
