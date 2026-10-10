module

public import Erdos993Lean.Analytic.V213.FiberRootLineCheck
public import Erdos993Lean.Analytic.V213.FiberProfileInverseBounds

/-!
Semantic consumers of all three accepted F09 pieces. Their actual
log tests prove the tangent slopes; the resulting bounds hold on the
complete closed pieces. Their actual convexity tests control every
point in each piece, not merely the upper endpoint.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Real Set

theorem fiber_root_line_parameters (id : FiberRootLineIdentity) :
    0 < lowMeanFractionReal (fiberRootLineById id).lo ∧
    lowMeanFractionReal (fiberRootLineById id).hi ≤ 3 / 5 ∧
    1 / 2 ≤ lowMeanFractionReal (fiberRootLineById id).v ∧
    lowMeanFractionReal (fiberRootLineById id).v < 1 ∧
    1 < lowMeanFractionReal (fiberRootLineById id).alpha ∧
    1 ≤ lowMeanFractionReal (fiberRootLineById id).beta ∧
    lowMeanFractionReal (fiberRootLineById id).beta ≤ 4 / 3 ∧
    0 < lowMeanFractionReal (fiberRootLineById id).epsilon_r ∧
    0 < lowMeanFractionReal (fiberRootLineById id).epsilon_c ∧
    lowMeanFractionReal (fiberRootLineById id).k =
      fiberProfileTangentK (lowMeanFractionReal (fiberRootLineById id).v) ∧
    lowMeanFractionReal (fiberRootLineById id).alpha =
      lowMeanFractionReal (fiberRootLineById id).v + lowMeanFractionReal (fiberRootLineById id).k ∧
    0 < lowMeanFractionReal (fiberRootLineById id).beta * lowMeanFractionReal (fiberRootLineById id).lo -
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1) := by
  cases id <;> norm_num [fiberRootLineById,lowMeanFractionReal,fiberProfileTangentK]

theorem fiber_root_line_log_test (id : FiberRootLineIdentity) :
    Real.log (fiberRootLineArgument id) < 2 * lowMeanFractionReal (fiberRootLineById id).v := by
  have hl := fiber_dyadic_log_bound (fiberRootLineById id).n (fiber_root_line_argument_domain id)
  have hg := fiber_root_line_strict_gap id .rootGap (by intro h; cases h)
  have hp := (fiber_root_line_parameters id).2.2.2.2.2.2.2.1
  change lowMeanFractionReal (fiberRootLineById id).epsilon_r <
    2 * lowMeanFractionReal (fiberRootLineById id).v -
      fiberDyadicLog (fiberRootLineById id).n (fiberRootLineArgument id) at hg
  linarith only [hl,hg,hp]

theorem fiber_root_line_bound (id : FiberRootLineIdentity) {t : ℝ}
    (ht : t ∈ Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi)) :
    fiberRayAroot t < lowMeanFractionReal (fiberRootLineById id).alpha -
      lowMeanFractionReal (fiberRootLineById id).beta * t := by
  have hp := fiber_root_line_parameters id
  have ht0 := hp.1.trans_le ht.1
  have hthi := ht.2.trans hp.2.1
  have ht1 : t < 1 := by linarith only [hthi]
  have hv : lowMeanFractionReal (fiberRootLineById id).v ∈ Ico (1 / 2 : ℝ) 1 :=
    ⟨hp.2.2.1,hp.2.2.2.1⟩
  have hk := hp.2.2.2.2.2.2.2.2.2.1
  have ha := hp.2.2.2.2.2.2.2.2.2.2.1
  have hl := fiber_root_line_log_test id
  unfold fiberRootLineArgument at hl
  rw [hk] at hl
  have hb0 : 0 < lowMeanFractionReal (fiberRootLineById id).beta := by
    linarith only [hp.2.2.2.2.2.1]
  have hslope := fiber_profile_root_slope_from_log hv.2 hb0 hl
  have h := fiber_profile_root_line ht0 ht1 (fiber_profile_actual_root_half ht0 hthi).le hv hslope
  rw [← hk] at h
  rw [ha]
  exact h

theorem fiber_root_line_piece_curvature (id : FiberRootLineIdentity) {t : ℝ}
    (ht : t ∈ Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi)) :
    0 < lowMeanFractionReal (fiberRootLineById id).beta * t -
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1) ∧
    15 < 4 * lowMeanFractionReal (fiberRootLineById id).beta *
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1) /
        (lowMeanFractionReal (fiberRootLineById id).beta * t -
          (lowMeanFractionReal (fiberRootLineById id).alpha - 1)) ^ 3 := by
  have hp := fiber_root_line_parameters id
  have hb0 : 0 ≤ lowMeanFractionReal (fiberRootLineById id).beta := by
    linarith only [hp.2.2.2.2.2.1]
  have hmlo := mul_le_mul_of_nonneg_left ht.1 hb0
  have hmhi := mul_le_mul_of_nonneg_left ht.2 hb0
  have hw : 0 < lowMeanFractionReal (fiberRootLineById id).beta * t -
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1) := by
    linarith only [hmlo,hp.2.2.2.2.2.2.2.2.2.2.2]
  have hc := fiber_root_line_strict_gap id .convexityGap (by intro h; cases h)
  change lowMeanFractionReal (fiberRootLineById id).epsilon_c <
    4 * lowMeanFractionReal (fiberRootLineById id).beta *
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1) -
        15 * (1 - lowMeanFractionReal (fiberRootLineById id).alpha +
          lowMeanFractionReal (fiberRootLineById id).beta * lowMeanFractionReal (fiberRootLineById id).hi) ^ 3 at hc
  have hpow : (lowMeanFractionReal (fiberRootLineById id).beta * t -
      (lowMeanFractionReal (fiberRootLineById id).alpha - 1)) ^ 3 ≤
        (1 - lowMeanFractionReal (fiberRootLineById id).alpha +
          lowMeanFractionReal (fiberRootLineById id).beta * lowMeanFractionReal (fiberRootLineById id).hi) ^ 3 := by
    exact pow_le_pow_left₀ hw.le (by linarith only [hmhi]) 3
  constructor
  · exact hw
  · apply (lt_div_iff₀ (pow_pos hw 3)).2
    nlinarith only [hc,hpow,hp.2.2.2.2.2.2.2.2.1]

end Erdos993Lean.Analytic.V213
