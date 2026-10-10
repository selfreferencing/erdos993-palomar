module

public import Erdos993Lean.Analytic.V213.FiberWingData
public import Erdos993Lean.Analytic.V213.FiberWingTaylor
public import Erdos993Lean.Analytic.V213.FiberEndpointPrinciple

/-!
Canonical full-shape binding of accepted F04 integer trees to Eq86,
the literal factorial Taylor sums and the signed Eq87 endpoint budget.
Every arithmetic leaf is tied to its typed printed row.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
namespace FiberWingFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)
def taylor4 (x : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (.add (.add (.add (.div (.pow x 0) (.atom (1,1)))
    (.div (.pow x 1) (.atom (1,1)))) (.div (.pow x 2) (.atom (2,1))))
    (.div (.pow x 3) (.atom (6,1)))) (.div (.pow x 4) (.atom (24,1)))
def taylor8 (x : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .add (.add (.add (.add (taylor4 x) (.div (.pow x 5) (.atom (120,1))))
    (.div (.pow x 6) (.atom (720,1)))) (.div (.pow x 7) (.atom (5040,1))))
    (.div (.pow x 8) (.atom (40320,1)))
def target (t : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.atom (10,1)) (.mul (.atom (9,2)) t)) (.div (.atom (9,2)) t)
def rate (n b s : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.div (.mul (sub (.atom (1,1)) (.pow b 2)) n) (.add n (.atom (1,1))))
    (.div (.mul (.mul (.atom (2,1)) b) s) (.add n (.atom (1,1)))))
    (.div (.mul (.pow b 2) n) (.mul (.atom (3,1)) (sub n (.atom (1,1)))))
def bonus (n a : LowMeanIntegerShape) : LowMeanIntegerShape :=
  .mul (.pow a 2) (sub n (.atom (1,1)))
def gain (a c : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (.mul c a) (.mul (.atom (21,5)) (.pow a 2))
def eta (n : LowMeanIntegerShape) : LowMeanIntegerShape := .div (sub n (.atom (2,1))) n
def gap (n t s d r : LowMeanIntegerShape) : LowMeanIntegerShape :=
  sub (sub (.add (.atom (1,1)) d)
    (.div (.mul (.atom (2,1)) (.pow s 2)) (.mul r (.add (.atom (1,1)) s))))
    (.mul (eta n) (target t))
end FiberWingFormula

def fiberWingShape (id : FiberWingIdentity) (role : FiberWingRole) : LowMeanIntegerShape :=
  let r := fiberWingById id
  let n := .atom r.N0
  let a := .atom r.a
  let b := .atom r.b
  let s := .atom r.s0
  let t := .atom r.tau
  match role with
  | .rate => FiberWingFormula.rate n b (.atom r.sqrtUpper)
  | .bonus => FiberWingFormula.bonus n a
  | .gain => FiberWingFormula.gain a (.atom r.gainCoefficient)
  | .rootSquare => FiberWingFormula.sub (.pow (.atom r.sqrtUpper) 2) n
  | .eta => FiberWingFormula.eta n
  | .width => FiberWingFormula.sub (.add (.mul (.atom r.mu_W) t) (.atom (2,1))) n
  | .taylorLeft => .mul (.pow (.add (.atom (1,1)) s) 2) (FiberWingFormula.taylor8 (.mul (.atom (2,1)) s))
  | .taylorRight => .mul (.pow t 5) (FiberWingFormula.taylor4 (.mul (.atom (2,1)) (.atom r.p)))
  | .gap => FiberWingFormula.gap n t s (.atom r.d) (.atom r.R)
  | .target => FiberWingFormula.target t

noncomputable def fiberWingValue (id : FiberWingIdentity) (role : FiberWingRole) : ℝ :=
  let r := fiberWingById id
  let n := lowMeanFractionReal r.N0
  let a := lowMeanFractionReal r.a
  let b := lowMeanFractionReal r.b
  let s := lowMeanFractionReal r.s0
  let t := lowMeanFractionReal r.tau
  match role with
  | .rate => (1 - b ^ 2) * n / (n + 1) - 2 * b * lowMeanFractionReal r.sqrtUpper / (n + 1) -
      b ^ 2 * n / (3 * (n - 1))
  | .bonus => a ^ 2 * (n - 1)
  | .gain => lowMeanFractionReal r.gainCoefficient * a - 21 * a ^ 2 / 5
  | .rootSquare => (lowMeanFractionReal r.sqrtUpper) ^ 2 - n
  | .eta => (n - 2) / n
  | .width => lowMeanFractionReal r.mu_W * t + 2 - n
  | .taylorLeft => (1 + s) ^ 2 * fiberWingTaylor8 (2 * s)
  | .taylorRight => t ^ 5 * fiberWingTaylor4 (2 * lowMeanFractionReal r.p)
  | .gap => 1 + lowMeanFractionReal r.d - 2 * s ^ 2 / (lowMeanFractionReal r.R * (1 + s)) -
      ((n - 2) / n) * fiberEndpointTarget 10 (9 / 2) t
  | .target => fiberEndpointTarget 10 (9 / 2) t

theorem fiber_wing_shape_real (id : FiberWingIdentity) (role : FiberWingRole) :
    lowMeanIntegerShapeReal (fiberWingShape id role) = fiberWingValue id role := by
  cases role <;> simp only [fiberWingShape,fiberWingValue,FiberWingFormula.rate,
    FiberWingFormula.bonus,FiberWingFormula.gain,FiberWingFormula.sub,FiberWingFormula.eta,
    FiberWingFormula.taylor4,FiberWingFormula.taylor8,FiberWingFormula.gap,FiberWingFormula.target,
    lowMeanIntegerShapeReal,fiberWingTaylor4,fiberWingTaylor8,fiberEndpointTarget,
    lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one] <;> norm_num <;> ring <;> simp

end Erdos993Lean.Analytic.V213
