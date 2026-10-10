module

public import Erdos993Lean.Analytic.V213.FiberProfileRootTransport

/-!
Root-line endpoint transport and whole-interval chord bounds for the
actual D/E profiles. The finite endpoint tests are uniform in the complete
skew interval. Root-line containment and convexity apply on closed pieces.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

noncomputable def fiberProfileRootLine (piece : FiberRootLineIdentity) (t : ℝ) : ℝ :=
  lowMeanFractionReal (fiberRootLineById piece).alpha -
    lowMeanFractionReal (fiberRootLineById piece).beta * t

theorem fiber_profile_control_line_endpoint (id : FiberProfileControlIdentity)
    (pid : FiberRationalProfileIdentity) (piece : FiberRootLineIdentity) {u : ℝ}
    (hp : (fiberProfileControlById id).profile = some pid)
    (ht : lowMeanFractionReal (fiberProfileControlById id).t ∈
      Icc (lowMeanFractionReal (fiberRootLineById piece).lo)
        (lowMeanFractionReal (fiberRootLineById piece).hi))
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberNamedProfile pid (lowMeanFractionReal (fiberProfileControlById id).t) u
      (fiberProfileRootLine piece (lowMeanFractionReal (fiberProfileControlById id).t)) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have hd := fiber_profile_control_endpoint_domain id
  have he := fiber_profile_control_endpoint_binding id
  have hline := fiber_root_line_bound piece ht
  have hfloor := fiber_profile_named_actual_root_floor pid hd.1
    (fiber_profile_control_time_cap id pid hp)
  have hcontains := fiber_root_endpoint_containment piece (fiberProfileControlById id).endpoint
    (by rwa [← he.1])
  rw [← he.1,← he.2] at hcontains
  have hline1 : fiberProfileRootLine piece (lowMeanFractionReal (fiberProfileControlById id).t) < 1 := by
    have hw := (fiber_root_line_piece_curvature piece ht).1
    unfold fiberProfileRootLine
    linarith only [hw]
  have hmono := fiber_profile_named_root_increases pid hd.1.le hu
    (hfloor.trans hline).le hline1 hd.2 hcontains
  have hb := fiber_profile_control_endpoint_bound id hu huR
  simp only [fiberProfileControlEnvelope,hp] at hb
  exact hmono.trans_lt hb

theorem fiber_profile_control_E_line_endpoint (id : FiberProfileControlIdentity)
    (piece : FiberRootLineIdentity) {u : ℝ}
    (ht : lowMeanFractionReal (fiberProfileControlById id).t ∈
      Icc (lowMeanFractionReal (fiberRootLineById piece).lo)
        (lowMeanFractionReal (fiberRootLineById piece).hi))
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberProfileE (lowMeanFractionReal (fiberProfileControlById id).t) u
      (fiberProfileRootLine piece (lowMeanFractionReal (fiberProfileControlById id).t)) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have hd := fiber_profile_control_endpoint_domain id
  have he := fiber_profile_control_endpoint_binding id
  have hline := fiber_root_line_bound piece ht
  have hcontains := fiber_root_endpoint_containment piece (fiberProfileControlById id).endpoint
    (by rwa [← he.1])
  rw [← he.1,← he.2] at hcontains
  have ht1 : lowMeanFractionReal (fiberProfileControlById id).t < 1 := by
    rw [he.1]
    cases (fiberProfileControlById id).endpoint <;>
      norm_num [fiberProfileEndpoint_t,lowMeanFractionReal]
  have hr := fiber_ray_root_formulas hd.1 ht1
  have hline1 : fiberProfileRootLine piece (lowMeanFractionReal (fiberProfileControlById id).t) < 1 := by
    have hw := (fiber_root_line_piece_curvature piece ht).1
    unfold fiberProfileRootLine
    linarith only [hw]
  have hmono := fiber_profile_E_root_increases hd.1.le hu (hr.1.trans hline).le
    hline1 hd.2 hcontains
  exact hmono.trans_lt (fiber_profile_control_E_cap id hu huR)

theorem fiber_profile_named_actual_to_line (pid : FiberRationalProfileIdentity)
    (piece : FiberRootLineIdentity) {t u : ℝ}
    (ht : t ∈ Icc (lowMeanFractionReal (fiberRootLineById piece).lo)
      (lowMeanFractionReal (fiberRootLineById piece).hi))
    (ht0 : 0 < t) (hcap : t ≤ fiberProfileTimeCap pid) (hu : 0 ≤ u) :
    fiberNamedProfile pid t u (fiberRayAroot t) ≤
      fiberNamedProfile pid t u (fiberProfileRootLine piece t) := by
  have hline := fiber_root_line_bound piece ht
  have hw := (fiber_root_line_piece_curvature piece ht).1
  exact fiber_profile_named_actual_root_transport pid ht0 hcap hu hline.le
    (by unfold fiberProfileRootLine; linarith only [hw])

theorem fiber_profile_E_actual_to_line (piece : FiberRootLineIdentity) {t u : ℝ}
    (ht : t ∈ Icc (lowMeanFractionReal (fiberRootLineById piece).lo)
      (lowMeanFractionReal (fiberRootLineById piece).hi))
    (ht0 : 0 < t) (ht1 : t < 1) (hu : 0 ≤ u) :
    fiberProfileE t u (fiberRayAroot t) ≤ fiberProfileE t u (fiberProfileRootLine piece t) := by
  have hline := fiber_root_line_bound piece ht
  have hw := (fiber_root_line_piece_curvature piece ht).1
  have hr := fiber_ray_root_formulas ht0 ht1
  exact fiber_profile_E_root_increases ht0.le hu hr.1.le hr.2.1
    (by unfold fiberProfileRootLine; linarith only [hw]) hline.le

end Erdos993Lean.Analytic.V213
