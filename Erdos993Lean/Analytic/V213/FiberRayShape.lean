module

public import Erdos993Lean.Analytic.V213.FiberRayData

/-!
Complete operation-shape and real interpretation of the accepted
Eq93 record trees. N is derived from the printed m_f+2 leaf, and all
root/gap shapes retain their exact parameter and threshold leaves.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

namespace FiberRayFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def rho (n r v : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let o := sub (.atom (1,1)) (.pow r 2)
  let m := .add n (.atom (1,1))
  sub (.div (.mul o n) m)
    (.mul (.add (.div (.atom (2,1)) m) (.div (.pow r 2) (.mul (.atom (3,1)) o))) v)

def kappa (n r v : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let o := sub (.atom (1,1)) (.pow r 2)
  let m := .add n (.atom (1,1))
  .add (.atom (2,1)) (.div (.mul (.mul (.atom (2,1)) m) v) (.mul (.mul (.atom (3,1)) n) o))

def error (n r s : LowMeanIntegerShape) : LowMeanIntegerShape :=
  let o := sub (.atom (1,1)) (.pow r 2)
  let m := .add n (.atom (1,1))
  .add (.add (.atom (1,2)) (.div (.mul (.mul (.atom (5,1)) r) s) (.mul (.atom (6,1)) o)))
    (.div (.add (.mul m (.pow r 2)) (.mul (.mul (.pow r 3) n) s)) (.mul (.atom (12,1)) (.pow o 2)))

end FiberRayFormula

def fiberRayShape (id : FiberRayIdentity) (role : FiberRayRole) : LowMeanIntegerShape :=
  let row := fiberRayById id
  let n := .add (.atom row.m_f) (.atom (2,1))
  let r := .atom row.R
  let s := .atom row.s
  let v := .atom row.v
  match role with
  | .rho => FiberRayFormula.rho n r v
  | .kappa => FiberRayFormula.kappa n r v
  | .error => FiberRayFormula.error n r s
  | .rhoGap => FiberRayFormula.sub (FiberRayFormula.rho n r v) (.atom row.rho_f)
  | .kappaGap => FiberRayFormula.sub (.atom row.k_f) (FiberRayFormula.kappa n r v)
  | .betaGap => FiberRayFormula.sub
      (.mul (.atom row.rho_f) (FiberRayFormula.sub (FiberRayFormula.sub n (.atom (1,1))) (.atom row.beta_f)))
      (.mul (.atom (2,1)) (FiberRayFormula.error n r s))
  | .squareGap => FiberRayFormula.sub
      (.mul (.mul (.atom row.d_f) (.pow (.atom row.rho_f) 2)) (.atom row.beta_f)) (.atom (4,1))
  | .sqrtS => FiberRayFormula.sub (.pow s 2) n
  | .sqrtV => FiberRayFormula.sub
      (.mul (.pow v 2) (FiberRayFormula.sub (.atom (1,1)) (.div (.atom (1,1)) n))) (.atom (1,1))

noncomputable def fiberRayRhoLower (N R v : ℝ) : ℝ :=
  (1 - R ^ 2) * N / (N + 1) - (2 / (N + 1) + R ^ 2 / (3 * (1 - R ^ 2))) * v

noncomputable def fiberRayKappaUpper (N R v : ℝ) : ℝ :=
  2 + 2 * (N + 1) * v / (3 * N * (1 - R ^ 2))

noncomputable def fiberRayErrorUpper (N R s : ℝ) : ℝ :=
  1 / 2 + 5 * R * s / (6 * (1 - R ^ 2)) +
    ((N + 1) * R ^ 2 + R ^ 3 * N * s) / (12 * (1 - R ^ 2) ^ 2)

noncomputable def fiberRayValue (id : FiberRayIdentity) (role : FiberRayRole) : ℝ :=
  let row := fiberRayById id
  let n := lowMeanFractionReal row.m_f + 2
  let r := lowMeanFractionReal row.R
  let s := lowMeanFractionReal row.s
  let v := lowMeanFractionReal row.v
  match role with
  | .rho => fiberRayRhoLower n r v
  | .kappa => fiberRayKappaUpper n r v
  | .error => fiberRayErrorUpper n r s
  | .rhoGap => fiberRayRhoLower n r v - lowMeanFractionReal row.rho_f
  | .kappaGap => lowMeanFractionReal row.k_f - fiberRayKappaUpper n r v
  | .betaGap => lowMeanFractionReal row.rho_f * (n - 1 - lowMeanFractionReal row.beta_f) -
      2 * fiberRayErrorUpper n r s
  | .squareGap => lowMeanFractionReal row.d_f * (lowMeanFractionReal row.rho_f) ^ 2 *
      lowMeanFractionReal row.beta_f - 4
  | .sqrtS => s ^ 2 - n
  | .sqrtV => v ^ 2 * (1 - 1 / n) - 1

theorem fiber_ray_shape_real (id : FiberRayIdentity) (role : FiberRayRole) :
    lowMeanIntegerShapeReal (fiberRayShape id role) = fiberRayValue id role := by
  cases role <;> simp only [fiberRayShape,fiberRayValue,FiberRayFormula.sub,FiberRayFormula.rho,
    FiberRayFormula.kappa,FiberRayFormula.error,lowMeanIntegerShapeReal,fiberRayRhoLower,
    fiberRayKappaUpper,fiberRayErrorUpper,lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,
    Int.cast_one,Nat.cast_one] <;> norm_num <;> ring

end Erdos993Lean.Analytic.V213
