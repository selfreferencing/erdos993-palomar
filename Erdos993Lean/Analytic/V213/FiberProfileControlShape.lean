module

public import Erdos993Lean.Analytic.V213.FiberProfileControlData
public import Erdos993Lean.Analytic.V213.FiberProfileCoefficients

/-!
Complete canonical shapes of all actual F10 endpoint coefficients
and selected E/V tests. The record coefficients come from the accepted
F08 typed record, with the exact c_f formula; the profile parameters and
endpoint arguments remain explicit leaves.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

def fiberRationalProfileRay : FiberRationalProfileIdentity → FiberRayIdentity
  | .a | .g => .a
  | .b => .b
  | .d => .d
  | .h => .h

namespace FiberProfileControlFormula

def sub (x y : LowMeanIntegerShape) : LowMeanIntegerShape := .add x (.neg y)

def coefficients (id : FiberProfileControlIdentity) :
    LowMeanIntegerShape × LowMeanIntegerShape × LowMeanIntegerShape :=
  let r := fiberProfileControlById id
  let t := .atom r.t
  let a := .atom r.a
  let one := .atom (1,1)
  let two := .atom (2,1)
  let G0 := .div (.pow a 2) (sub one a)
  let base := sub (.mul (.mul two t) G0) (.mul (.atom (9,2)) (.pow (sub one t) 2))
  match r.profile with
  | none =>
      (base,.div (.mul (.mul (.atom (97,1)) t) G0) (.mul (.atom (140,1)) (.atom (63,100))),
        .mul t (sub (.add (.div (.mul (.atom (17,6)) G0) (.atom (63,100))) one)
          (.mul two (.add (.mul (.atom (19,1)) t) two))))
  | some pid =>
      let p := fiberRationalProfileById pid
      let ray := fiberRayById (fiberRationalProfileRay pid)
      let m := .atom p.m
      let s := .atom p.s
      let ra := .atom p.ra
      let rho := .atom ray.rho_f
      let kappa := .atom ray.k_f
      let df := .atom ray.d_f
      let mf := .atom ray.m_f
      let delta := .div one (sub one (.pow ra 2))
      let cf := .div (.pow (.add (.atom (77,20)) (.div (.atom (10,1)) mf)) 2)
        (.add mf (.atom (3,1)))
      let C := .add (.add (sub (.neg (.mul (.atom (6,1)) a)) two)
        (.div (.mul (sub df (.atom (11,10))) a) (sub one a)))
        (.div cf (.mul (sub one a) (sub two a)))
      let N := .add (.mul m t) two
      let target := .add (.atom p.b) (.mul (.atom p.beta) (sub t one))
      (.add (.add base target) (.div C m),
        .div (.mul (.mul two G0) (.add N (.pow s 2))) (.mul (.mul s rho) m),
        .mul (.div N m) (sub (.add (.div (.mul kappa G0) rho) delta) (.mul delta N)))

end FiberProfileControlFormula

def fiberProfileControlShape (id : FiberProfileControlIdentity) (role : FiberProfileControlRole) :
    LowMeanIntegerShape :=
  let r := fiberProfileControlById id
  let cs := FiberProfileControlFormula.coefficients id
  let c0 := cs.1
  let c1 := cs.2.1
  let c2 := cs.2.2
  match role with
  | .c0 => c0
  | .c1 => c1
  | .c2 => c2
  | .firstTest => if r.increasing then .add c1 (.mul (.mul (.atom (2,1)) c2) (.atom r.R)) else .neg c2
  | .secondTest => if r.increasing then FiberProfileControlFormula.sub
      (FiberProfileControlFormula.sub (FiberProfileControlFormula.sub (.atom r.z) c0)
        (.mul c1 (.atom r.R))) (.mul c2 (.pow (.atom r.R) 2))
    else FiberProfileControlFormula.sub
      (.mul (.mul (.atom (4,1)) (.neg c2)) (FiberProfileControlFormula.sub (.atom r.z) c0)) (.pow c1 2)

noncomputable def fiberProfileControlCoefficients (id : FiberProfileControlIdentity) : ℝ × ℝ × ℝ :=
  let r := fiberProfileControlById id
  let t := lowMeanFractionReal r.t
  let a := lowMeanFractionReal r.a
  match r.profile with
  | none => (fiberProfileF t a,fiberProfileELinear t a,fiberProfileEQuadratic t a)
  | some pid =>
      let p := fiberRationalProfileById pid
      let ray := fiberRayById (fiberRationalProfileRay pid)
      let cf := fiberRayCF (lowMeanFractionReal ray.m_f)
      let df := lowMeanFractionReal ray.d_f
      let rho := lowMeanFractionReal ray.rho_f
      let kappa := lowMeanFractionReal ray.k_f
      let m := lowMeanFractionReal p.m
      let s := lowMeanFractionReal p.s
      let delta := fiberRayDelta (lowMeanFractionReal p.ra)
      (fiberProfileDConstant cf df m (lowMeanFractionReal p.b) (lowMeanFractionReal p.beta) t a,
        fiberProfileDLinear rho m s t a,fiberProfileDQuadratic rho kappa m delta t a)

noncomputable def fiberProfileControlValue (id : FiberProfileControlIdentity) (role : FiberProfileControlRole) : ℝ :=
  let r := fiberProfileControlById id
  let cs := fiberProfileControlCoefficients id
  match role with
  | .c0 => cs.1
  | .c1 => cs.2.1
  | .c2 => cs.2.2
  | .firstTest => if r.increasing then cs.2.1 + 2 * cs.2.2 * lowMeanFractionReal r.R else -cs.2.2
  | .secondTest => if r.increasing then lowMeanFractionReal r.z - cs.1 -
      cs.2.1 * lowMeanFractionReal r.R - cs.2.2 * lowMeanFractionReal r.R ^ 2
    else 4 * (-cs.2.2) * (lowMeanFractionReal r.z - cs.1) - cs.2.1 ^ 2

theorem fiber_profile_control_coefficients_real (id : FiberProfileControlIdentity) :
    lowMeanIntegerShapeReal (FiberProfileControlFormula.coefficients id).1 =
        (fiberProfileControlCoefficients id).1 ∧
      lowMeanIntegerShapeReal (FiberProfileControlFormula.coefficients id).2.1 =
        (fiberProfileControlCoefficients id).2.1 ∧
      lowMeanIntegerShapeReal (FiberProfileControlFormula.coefficients id).2.2 =
        (fiberProfileControlCoefficients id).2.2 := by
  cases hp : (fiberProfileControlById id).profile <;>
    simp only [FiberProfileControlFormula.coefficients,fiberProfileControlCoefficients,hp,
      FiberProfileControlFormula.sub,lowMeanIntegerShapeReal,lowMeanFractionReal,
      fiberProfileF,fiberProfileG0,fiberProfileC,fiberProfileDConstant,fiberProfileDLinear,
      fiberProfileDQuadratic,fiberProfileELinear,fiberProfileEQuadratic,fiberRayCF,fiberRayDelta,
      inv_eq_one_div,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,div_one] <;>
    norm_num <;> constructor <;> first | ring | constructor <;> ring
  all_goals simp

theorem fiber_profile_control_shape_real (id : FiberProfileControlIdentity) (role : FiberProfileControlRole) :
    lowMeanIntegerShapeReal (fiberProfileControlShape id role) = fiberProfileControlValue id role := by
  have h := fiber_profile_control_coefficients_real id
  cases role <;> simp only [fiberProfileControlShape,fiberProfileControlValue,
    FiberProfileControlFormula.sub,lowMeanIntegerShapeReal,h.1,h.2.1,h.2.2,
    lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,Int.cast_one,Nat.cast_one,div_one]
  all_goals
    split <;> simp only [FiberProfileControlFormula.sub,lowMeanIntegerShapeReal,
      h.1,h.2.1,h.2.2,lowMeanFractionReal,Int.cast_ofNat,Nat.cast_ofNat,
      Int.cast_one,Nat.cast_one,div_one] <;> norm_num <;> ring <;> simp

noncomputable def fiberProfileControlEnvelope (id : FiberProfileControlIdentity) (u : ℝ) : ℝ :=
  let r := fiberProfileControlById id
  match r.profile with
  | none => fiberProfileE (lowMeanFractionReal r.t) u (lowMeanFractionReal r.a)
  | some pid =>
      let p := fiberRationalProfileById pid
      let ray := fiberRayById (fiberRationalProfileRay pid)
      fiberProfileD (fiberRayCF (lowMeanFractionReal ray.m_f)) (lowMeanFractionReal ray.d_f)
        (lowMeanFractionReal ray.rho_f) (lowMeanFractionReal ray.k_f)
        (lowMeanFractionReal p.m) (lowMeanFractionReal p.s) (fiberRayDelta (lowMeanFractionReal p.ra))
        (lowMeanFractionReal p.b) (lowMeanFractionReal p.beta) (lowMeanFractionReal r.t) u (lowMeanFractionReal r.a)

theorem fiber_profile_control_polynomial (id : FiberProfileControlIdentity) (u : ℝ) :
    fiberProfileControlEnvelope id u = (fiberProfileControlCoefficients id).1 +
      (fiberProfileControlCoefficients id).2.1 * u + (fiberProfileControlCoefficients id).2.2 * u ^ 2 := by
  cases hp : (fiberProfileControlById id).profile <;>
    simp only [fiberProfileControlEnvelope,fiberProfileControlCoefficients,hp,
      fiber_profile_D_polynomial,fiber_profile_E_polynomial]

end Erdos993Lean.Analytic.V213
