module

public import Erdos993Lean.Analytic.V213.FiberProfileControlShape
public import Erdos993Lean.Analytic.V213.FiberProfileConvexity

/-!
The five literal rational-profile parameter domains. These small
closed scalar identities/inequalities use the accepted F08/F10 typed
tables and exact real casts of their Int/Nat pairs. No Rat evaluator,
unprinted endpoint, or assumption about a concrete input is used.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213

noncomputable def fiberNamedProfile (id : FiberRationalProfileIdentity) (t u a : ℝ) : ℝ :=
  let p := fiberRationalProfileById id
  let r := fiberRayById (fiberRationalProfileRay id)
  fiberProfileD (fiberRayCF (lowMeanFractionReal r.m_f)) (lowMeanFractionReal r.d_f)
    (lowMeanFractionReal r.rho_f) (lowMeanFractionReal r.k_f)
    (lowMeanFractionReal p.m) (lowMeanFractionReal p.s) (fiberRayDelta (lowMeanFractionReal p.ra))
    (lowMeanFractionReal p.b) (lowMeanFractionReal p.beta) t u a

noncomputable def fiberProfileRootFloor : FiberRationalProfileIdentity → ℝ
  | .h => 3 / 4
  | _ => 1 / 2

noncomputable def fiberProfileTimeCap : FiberRationalProfileIdentity → ℝ
  | .h => 19 / 50
  | .g => 11 / 25
  | .d => 13 / 25
  | _ => 3 / 5

theorem fiber_profile_parameters (id : FiberRationalProfileIdentity) :
    let p := fiberRationalProfileById id
    let r := fiberRayById (fiberRationalProfileRay id)
    let cf := fiberRayCF (lowMeanFractionReal r.m_f)
    let delta := fiberRayDelta (lowMeanFractionReal p.ra)
    19 ≤ lowMeanFractionReal p.m ∧ 0 < lowMeanFractionReal p.s ∧
      0 ≤ lowMeanFractionReal p.ra ∧ lowMeanFractionReal p.ra ≤ 1 / 2 ∧
      0 < lowMeanFractionReal r.rho_f ∧ 0 ≤ lowMeanFractionReal r.k_f ∧
      0 ≤ cf ∧ cf ≤ 12 / 5 ∧ 0 ≤ cf + lowMeanFractionReal r.d_f - 11 / 10 ∧
      0 ≤ delta ∧ delta * lowMeanFractionReal p.m * (lowMeanFractionReal r.R) ^ 2 ≤ 7 / 2 ∧
      0 < lowMeanFractionReal r.R ∧ lowMeanFractionReal r.R ≤ 7 / 25 ∧
      0 < fiberProfileRootFloor id ∧ fiberProfileTimeCap id ≤ 3 / 5 := by
  cases id <;> norm_num [fiberRationalProfileById,fiberRationalProfileRay,fiberRayById,
    fiberRayCF,fiberRayDelta,lowMeanFractionReal,fiberProfileRootFloor,fiberProfileTimeCap]

theorem fiber_profile_named_piece_convex (id : FiberRationalProfileIdentity)
    (piece : FiberRootLineIdentity) {u : ℝ}
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).R) :
    ConvexOn ℝ (Set.Icc (lowMeanFractionReal (fiberRootLineById piece).lo)
      (lowMeanFractionReal (fiberRootLineById piece).hi))
      (fun t => fiberNamedProfile id t u (lowMeanFractionReal (fiberRootLineById piece).alpha -
        lowMeanFractionReal (fiberRootLineById piece).beta * t)) := by
  rcases fiber_profile_parameters id with
    ⟨hm,hs,hra,hrah,hr,hk,hcf0,hcf,hcd,hd,hloss,hR,hRh,hfloor,htcap⟩
  exact fiber_profile_D_piece_convex piece hr hk hm hs hcf0 hcf hcd hd hu huR hloss

end Erdos993Lean.Analytic.V213
