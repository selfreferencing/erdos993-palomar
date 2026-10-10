module

public import Erdos993Lean.Analytic.V213.FiberProfileParameters
public import Erdos993Lean.Analytic.V213.FiberProfileRootMonotonicity
public import Erdos993Lean.Analytic.V213.FiberProfileInverseBounds
public import Erdos993Lean.Analytic.V213.FiberProfileControlMetadata
public import Erdos993Lean.Analytic.V213.FiberRootEndpointCheck

/-!
Actual-root transport for each of the five named profiles. The
common/H C derivative domains are retained explicitly, then discharged
for the actual inverse root on each printed time range. The endpoint
consumer combines the actual F09 root with the actual F10 quadratics.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

theorem fiber_profile_named_C_increases (id : FiberRationalProfileIdentity) {a a' : ℝ}
    (ha : fiberProfileRootFloor id ≤ a) (hah : a < 1) (ha'h : a' < 1) (haa' : a ≤ a') :
    fiberProfileC (fiberRayCF (lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).m_f))
      (lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).d_f) a ≤
    fiberProfileC (fiberRayCF (lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).m_f))
      (lowMeanFractionReal (fiberRayById (fiberRationalProfileRay id)).d_f) a' := by
  cases id <;> norm_num [fiberRationalProfileRay,fiberRayById,fiberProfileRootFloor,
    lowMeanFractionReal,fiberRayCF] at ha ⊢
  all_goals first
    | exact (fiber_profile_C_common_increases (by norm_num)).monotoneOn
        ⟨ha,hah⟩ ⟨ha.trans haa',ha'h⟩ haa'
    | exact fiber_profile_C_H_increases.monotoneOn
        ⟨ha,hah⟩ ⟨ha.trans haa',ha'h⟩ haa'

theorem fiber_profile_named_root_increases (id : FiberRationalProfileIdentity) {t u a a' : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (ha : fiberProfileRootFloor id ≤ a)
    (hah : a < 1) (ha'h : a' < 1) (haa' : a ≤ a') :
    fiberNamedProfile id t u a ≤ fiberNamedProfile id t u a' := by
  rcases fiber_profile_parameters id with
    ⟨hm,hs,hra,hrah,hr,hk,hcf0,hcf,hcd,hd,hloss,hR,hRh,hfloor,htcap⟩
  have hm0 : 0 < lowMeanFractionReal (fiberRationalProfileById id).m := by linarith only [hm]
  exact fiber_profile_D_root_increases hr hk hm0 hs ht hu (hfloor.le.trans ha) hah ha'h haa'
    (fiber_profile_named_C_increases id ha hah ha'h haa')

theorem fiber_profile_named_actual_root_floor (id : FiberRationalProfileIdentity) {t : ℝ}
    (ht : 0 < t) (hcap : t ≤ fiberProfileTimeCap id) :
    fiberProfileRootFloor id < fiberRayAroot t := by
  cases id with
  | h => exact fiber_profile_actual_root_three_quarters ht hcap
  | a => exact fiber_profile_actual_root_half ht hcap
  | b => exact fiber_profile_actual_root_half ht hcap
  | d =>
      exact fiber_profile_actual_root_half ht (hcap.trans (by norm_num [fiberProfileTimeCap]))
  | g =>
      exact fiber_profile_actual_root_half ht (hcap.trans (by norm_num [fiberProfileTimeCap]))

theorem fiber_profile_named_actual_root_transport (id : FiberRationalProfileIdentity) {t u a : ℝ}
    (ht : 0 < t) (hcap : t ≤ fiberProfileTimeCap id) (hu : 0 ≤ u)
    (ha : fiberRayAroot t ≤ a) (ha1 : a < 1) :
    fiberNamedProfile id t u (fiberRayAroot t) ≤ fiberNamedProfile id t u a := by
  rcases fiber_profile_parameters id with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hth⟩
  have ht1 : t < 1 := by linarith only [hcap,hth]
  have hroot := fiber_ray_root_formulas ht ht1
  exact fiber_profile_named_root_increases id ht.le hu
    (fiber_profile_named_actual_root_floor id ht hcap).le hroot.2.1 ha1 ha

theorem fiber_profile_control_actual_root_bound (id : FiberProfileControlIdentity)
    (pid : FiberRationalProfileIdentity) {u : ℝ}
    (hp : (fiberProfileControlById id).profile = some pid)
    (ht : 0 < lowMeanFractionReal (fiberProfileControlById id).t)
    (hcap : lowMeanFractionReal (fiberProfileControlById id).t ≤ fiberProfileTimeCap pid)
    (ha1 : lowMeanFractionReal (fiberProfileControlById id).a < 1)
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberNamedProfile pid (lowMeanFractionReal (fiberProfileControlById id).t) u
      (fiberRayAroot (lowMeanFractionReal (fiberProfileControlById id).t)) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have he := fiber_profile_control_endpoint_binding id
  have ha := fiber_root_endpoint_actual (fiberProfileControlById id).endpoint
  rw [← he.1,← he.2] at ha
  have hroot := fiber_profile_named_actual_root_transport pid ht hcap hu ha.le ha1
  have hb := fiber_profile_control_endpoint_bound id hu huR
  simp only [fiberProfileControlEnvelope,hp] at hb
  exact hroot.trans_lt hb

theorem fiber_profile_control_actual_endpoint (id : FiberProfileControlIdentity)
    (pid : FiberRationalProfileIdentity) {u : ℝ}
    (hp : (fiberProfileControlById id).profile = some pid)
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberNamedProfile pid (lowMeanFractionReal (fiberProfileControlById id).t) u
      (fiberRayAroot (lowMeanFractionReal (fiberProfileControlById id).t)) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have hd := fiber_profile_control_endpoint_domain id
  exact fiber_profile_control_actual_root_bound id pid hp hd.1
    (fiber_profile_control_time_cap id pid hp) hd.2 hu huR

theorem fiber_profile_control_actual_E_endpoint (id : FiberProfileControlIdentity) {u : ℝ}
    (hu : 0 ≤ u) (huR : u ≤ lowMeanFractionReal (fiberProfileControlById id).R) :
    fiberProfileE (lowMeanFractionReal (fiberProfileControlById id).t) u
      (fiberRayAroot (lowMeanFractionReal (fiberProfileControlById id).t)) <
        lowMeanFractionReal (fiberProfileControlById id).z := by
  have hd := fiber_profile_control_endpoint_domain id
  have he := fiber_profile_control_endpoint_binding id
  have ha := fiber_root_endpoint_actual (fiberProfileControlById id).endpoint
  rw [← he.1,← he.2] at ha
  have ht1 : lowMeanFractionReal (fiberProfileControlById id).t < 1 := by
    rw [he.1]
    cases (fiberProfileControlById id).endpoint <;>
      norm_num [fiberProfileEndpoint_t,lowMeanFractionReal]
  have hroot := fiber_ray_root_formulas hd.1 ht1
  have hmono := fiber_profile_E_root_increases hd.1.le hu hroot.1.le
    hroot.2.1 hd.2 ha.le
  exact hmono.trans_lt (fiber_profile_control_E_cap id hu huR)

end Erdos993Lean.Analytic.V213
