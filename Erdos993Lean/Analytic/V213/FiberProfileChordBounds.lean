module

public import Erdos993Lean.Analytic.V213.FiberProfileChordCheck

/-!
Actual closed-interval chord bounds for all twelve consecutive
printed controls. Each whole root-line piece is proved convex at fixed
skew; restriction to the exact control interval preserves convexity.
Actual-root transport and both uniform endpoint tests are consumed.

-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

noncomputable def fiberProfileChordValue (id : FiberProfileChordIdentity) (t : ℝ) : ℝ :=
  let c := fiberProfileChordById id
  let l := fiberProfileControlById c.left
  let h := fiberProfileControlById c.right
  (lowMeanFractionReal h.t - t) / (lowMeanFractionReal h.t - lowMeanFractionReal l.t) *
    lowMeanFractionReal l.z +
  (t - lowMeanFractionReal l.t) / (lowMeanFractionReal h.t - lowMeanFractionReal l.t) *
    lowMeanFractionReal h.z

theorem fiber_profile_chord_bound (id : FiberProfileChordIdentity) {t u : ℝ}
    (ht : t ∈ Icc (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById id).left).t)
      (lowMeanFractionReal (fiberProfileControlById (fiberProfileChordById id).right).t))
    (hu : 0 ≤ u)
    (huR : u ≤ lowMeanFractionReal (fiberRayById
      (fiberRationalProfileRay (fiberProfileChordById id).profile)).R) :
    max 0 (max (fiberNamedProfile (fiberProfileChordById id).profile t u (fiberRayAroot t))
      (fiberProfileE t u (fiberRayAroot t))) ≤ fiberProfileChordValue id t := by
  let c := fiberProfileChordById id
  let l := fiberProfileControlById c.left
  let h := fiberProfileControlById c.right
  let p := fiberRootLineById c.piece
  have hg := fiber_profile_chord_geometry id
  change l.profile = some c.profile ∧ h.profile = some c.profile ∧
    l.R = (fiberRayById (fiberRationalProfileRay c.profile)).R ∧
    h.R = (fiberRayById (fiberRationalProfileRay c.profile)).R ∧
    lowMeanFractionReal l.t < lowMeanFractionReal h.t ∧
    lowMeanFractionReal p.lo ≤ lowMeanFractionReal l.t ∧
    lowMeanFractionReal h.t ≤ lowMeanFractionReal p.hi ∧
    0 ≤ lowMeanFractionReal l.z ∧ 0 ≤ lowMeanFractionReal h.z at hg
  rcases hg with ⟨hpL,hpR,hRL,hRR,hlh,hlo,hhi,hzl,hzh⟩
  change t ∈ Icc (lowMeanFractionReal l.t) (lowMeanFractionReal h.t) at ht
  have hlmem : lowMeanFractionReal l.t ∈ Icc (lowMeanFractionReal p.lo) (lowMeanFractionReal p.hi) :=
    ⟨hlo,hlh.le.trans hhi⟩
  have hhmem : lowMeanFractionReal h.t ∈ Icc (lowMeanFractionReal p.lo) (lowMeanFractionReal p.hi) :=
    ⟨hlo.trans hlh.le,hhi⟩
  have hwhole : t ∈ Icc (lowMeanFractionReal p.lo) (lowMeanFractionReal p.hi) :=
    ⟨hlo.trans ht.1,ht.2.trans hhi⟩
  have ht0 : 0 < t := (fiber_profile_control_endpoint_domain c.left).1.trans_le ht.1
  have hcap : t ≤ fiberProfileTimeCap c.profile := ht.2.trans
    (fiber_profile_control_time_cap c.right c.profile hpR)
  rcases fiber_profile_parameters c.profile with
    ⟨_,_,_,_,_,_,_,_,_,_,_,_,hRh,_,hth⟩
  have ht1 : t < 1 := by linarith only [hcap,hth]
  have huE : u ≤ 7 / 25 := huR.trans hRh
  have hRLo : u ≤ lowMeanFractionReal l.R := by rwa [hRL]
  have hRHi : u ≤ lowMeanFractionReal h.R := by rwa [hRR]
  have hDl := fiber_profile_control_line_endpoint c.left c.profile c.piece hpL hlmem hu hRLo
  have hDh := fiber_profile_control_line_endpoint c.right c.profile c.piece hpR hhmem hu hRHi
  have hEl := fiber_profile_control_E_line_endpoint c.left c.piece hlmem hu hRLo
  have hEh := fiber_profile_control_E_line_endpoint c.right c.piece hhmem hu hRHi
  have hDwhole := fiber_profile_named_piece_convex c.profile c.piece hu huR
  have hDconv : ConvexOn ℝ (Icc (lowMeanFractionReal l.t) (lowMeanFractionReal h.t))
      (fun x => fiberNamedProfile c.profile x u (fiberProfileRootLine c.piece x)) :=
    hDwhole.subset (by intro x hx; exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩) (convex_Icc _ _)
  have hEwhole := fiber_profile_E_piece_convex c.piece hu huE
  have hEconv : ConvexOn ℝ (Icc (lowMeanFractionReal l.t) (lowMeanFractionReal h.t))
      (fun x => fiberProfileE x u (fiberProfileRootLine c.piece x)) :=
    hEwhole.subset (by intro x hx; exact ⟨hlo.trans hx.1,hx.2.trans hhi⟩) (convex_Icc _ _)
  have hDb := fiber_convex_chord hlh ht hDconv hDl.le hDh.le
  have hEb := fiber_convex_chord hlh ht hEconv hEl.le hEh.le
  have hDactual := (fiber_profile_named_actual_to_line c.profile c.piece hwhole ht0 hcap hu).trans hDb
  have hEactual := (fiber_profile_E_actual_to_line c.piece hwhole ht0 ht1 hu).trans hEb
  have hc0 : 0 ≤ fiberProfileChordValue id t := by
    exact add_nonneg
      (mul_nonneg (div_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hlh).le) hzl)
      (mul_nonneg (div_nonneg (sub_nonneg.mpr ht.1) (sub_pos.mpr hlh).le) hzh)
  exact max_le hc0 (max_le hDactual hEactual)

end Erdos993Lean.Analytic.V213
