module

public import Erdos993Lean.Analytic.V213.FiberOuterStartData
public import Erdos993Lean.Analytic.V213.FiberOuterEndpointGeometry
public import Erdos993Lean.Analytic.V213.FiberOuterDefinitions

/-!
Canonical binding of accepted F05 integer trees to the printed
P_N, R_N, Delta_N, logarithm, target and Eq80 endpoint-budget formulas.
All operation shapes include their actual parameter leaves. Row lookup
is by printed identity; no numerical position defines a paper record.
-/

@[expose] public section

namespace Erdos993Lean.Analytic.V213

namespace FiberOuterFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def D (m : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (sub (.atom (51,20)) (.div (.atom (1,1)) (sub m (.atom (2,1))))) m

def C (m y : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let ay := sub (.atom (1,1)) y
  sub (sub
    (.div (.pow (sub (.mul (sub (.atom (1,1)) (.div y (.mul (.atom (3,1)) ay))) m) (.atom (4,1))) 2)
      (.mul (.atom (2,1)) m))
    (.div (sub m (.atom (1,1))) (.mul (.mul (.atom (6,1)) ay) (sub m (.atom (2,1))))))
    (.div (.mul y m) (.mul (.atom (12,1)) (.pow ay 2)))

def chi (n : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.atom (1,1)) (.div (.atom (1,1)) (.mul (.atom (2,1)) n)))
    (.div (.atom (1,1)) (.mul (.atom (6,1)) (.pow n 2)))

def P (n a : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let m := .add n (.atom (1,1))
  let y := .pow a 2
  .add (D m) (.mul y (C m y))

def R (n a : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let m := .add n (.atom (1,1))
  let y := .pow a 2
  let ay := sub (.atom (1,1)) y
  sub (.div (.mul ay n) m)
    (.div (.add (.div (.atom (2,1)) m) (.div y (.mul (.atom (3,1)) ay))) (chi n))

def delta (n a : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let y := .pow a 2
  .mul (.div y (sub (.atom (1,1)) y))
    (.add (sub n (.atom (1,1))) (.div (.atom (1,1)) n))

def logBound (s : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let z := .div (sub (.atom (1,1)) s) (.add (.atom (1,1)) s)
  .mul (.atom (2,1)) (.add (.add z (.div (.pow z 3) (.atom (3,1))))
    (.div (.pow z 5) (.mul (.atom (5,1)) (sub (.atom (1,1)) (.pow z 2)))))

def target (s b beta : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.add (.atom (10,1)) beta) (.mul (.atom (9,2)) s))
    (.div (sub (.add (.atom (9,2)) beta) b) s)

def barrier (v : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .div (.pow v 2) (.add (sub (.atom (4,1)) v) (.div (.pow v 2) (.atom (48,1))))

def gap (n s b beta d v rate : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.add (.atom (1,1)) d) (.div (.mul (.atom (2,1)) (barrier v)) rate))
    (.mul (.div (sub n (.atom (2,1))) n) (target s b beta))

end FiberOuterFormula

def fiberOuterStartShape (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) : LowMeanIntegerShape :=
  let r := fiberOuterStartById id
  let n := .atom r.n
  let a := .atom r.a
  let s := .atom r.sigma
  let b := .atom r.b0
  let beta := .atom r.beta0
  match role with
  | .gain => FiberOuterFormula.P n a
  | .rate => FiberOuterFormula.R n a
  | .bonus => FiberOuterFormula.delta n a
  | .logarithm => FiberOuterFormula.logBound s
  | .target => FiberOuterFormula.target s b beta
  | .gap => FiberOuterFormula.gap n s b beta (.atom r.d_star) (.atom r.v_star) (.atom r.R_star)

noncomputable def fiberOuterStartValue (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) : ℝ :=
  let r := fiberOuterStartById id
  let n := lowMeanFractionReal r.n
  let a := lowMeanFractionReal r.a
  let s := lowMeanFractionReal r.sigma
  let b := lowMeanFractionReal r.b0
  let beta := lowMeanFractionReal r.beta0
  let v := lowMeanFractionReal r.v_star
  match role with
  | .gain => fiberOuterP n (a ^ 2)
  | .rate => fiberOuterR n (a ^ 2)
  | .bonus => fiberOuterDelta n (a ^ 2)
  | .logarithm => fiberOuterLogBound ((1 - s) / (1 + s))
  | .target => fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) s
  | .gap => 1 + lowMeanFractionReal r.d_star -
      2 * (v ^ 2 / (4 - v + v ^ 2 / 48)) / lowMeanFractionReal r.R_star -
      ((n - 2) / n) * fiberEndpointTarget (10 + beta) (9 / 2 + beta - b) s

theorem fiber_outer_gain_D_rational {m : ℝ} (hm : 2 < m) :
    fiberGainD m = (51 / 20 - 1 / (m - 2)) / m := by
  have hm0 : 0 < m := by linarith only [hm]
  have hm2 : 0 < m - 2 := by linarith only [hm]
  unfold fiberGainD
  field_simp [hm0.ne',hm2.ne']
  ring

theorem fiber_outer_start_shape_real (id : FiberOuterStartIdentity) (role : FiberOuterStartRole) :
    lowMeanIntegerShapeReal (fiberOuterStartShape id role) = fiberOuterStartValue id role := by
  have hm : 2 < lowMeanFractionReal (fiberOuterStartById id).n + 1 := by
    cases id <;> norm_num [fiberOuterStartById,lowMeanFractionReal]
  cases role <;> simp only [fiberOuterStartValue,fiberOuterP] <;>
    (try rw [fiber_outer_gain_D_rational hm]) <;>
    simp only [fiberOuterStartShape,fiberOuterStartValue,FiberOuterFormula.P,FiberOuterFormula.R,
      FiberOuterFormula.delta,FiberOuterFormula.logBound,FiberOuterFormula.target,FiberOuterFormula.gap,
      FiberOuterFormula.barrier,FiberOuterFormula.D,FiberOuterFormula.C,FiberOuterFormula.chi,
      FiberOuterFormula.sub,lowMeanIntegerShapeReal,fiberOuterP,fiberOuterC,
      fiberOuterR,fiberOuterChi,fiberOuterDelta,fiberOuterLogBound,fiberEndpointTarget,
      lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one]
    <;> norm_num <;> ring

end Erdos993Lean.Analytic.V213
