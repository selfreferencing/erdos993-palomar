module

public import Erdos993Lean.Analytic.V213.FiberProfileCurvature
public import Erdos993Lean.Analytic.V213.FiberRootLineGeometry

/-!
Whole-piece convexity of the actual Eq94/95 profiles at each named
accepted F09 line. The derivative formulas are for the actual functions;
the kernel-checked convexity gap discharges the line curvature at every
point of each closed piece.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Set

theorem fiber_profile_D_piece_convex (id : FiberRootLineIdentity)
    {cf df rho kappa m s delta b targetBeta u R : ℝ}
    (hr : 0 < rho) (hk : 0 ≤ kappa) (hm : 19 ≤ m) (hs : 0 < s)
    (hcf0 : 0 ≤ cf) (hcf : cf ≤ 12 / 5) (hc : 0 ≤ cf + df - 11 / 10)
    (hd : 0 ≤ delta) (hu : 0 ≤ u) (huR : u ≤ R)
    (hloss : delta * m * R ^ 2 ≤ 7 / 2) :
    ConvexOn ℝ (Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi))
      (fun t => fiberProfileD cf df rho kappa m s delta b targetBeta t u
        (lowMeanFractionReal (fiberRootLineById id).alpha - lowMeanFractionReal (fiberRootLineById id).beta * t)) := by
  let alpha := lowMeanFractionReal (fiberRootLineById id).alpha
  let beta := lowMeanFractionReal (fiberRootLineById id).beta
  have hp := fiber_root_line_parameters id
  have ha : 1 < alpha := hp.2.2.2.2.1
  have hb : 1 ≤ beta := hp.2.2.2.2.2.1
  have hbhi : beta ≤ 4 / 3 := hp.2.2.2.2.2.2.1
  have hm0 : 0 < m := by linarith only [hm]
  have hb0 : 0 < beta := by linarith only [hb]
  have hconv : ConvexOn ℝ (Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi))
      (fiberProfileLine (fiberProfileDP2 rho kappa m s delta beta u)
        (fiberProfileDP1 rho kappa m s delta targetBeta alpha beta u)
        (fiberProfileDP0 df rho kappa m s delta b targetBeta alpha beta u)
        (fiberProfileDK cf df rho kappa m s alpha beta u) (cf / m) beta (alpha - 1)) := by
    apply fiber_profile_line_convex
    · intro t ht
      exact (fiber_root_line_piece_curvature id ht).1
    · intro t ht
      have hg := fiber_root_line_piece_curvature id ht
      exact (fiber_profile_D_second_strict hr hk hm hs hcf0 hcf hc hd hu huR hloss ha hb hbhi hg.1 hg.2).le
        |>.trans' (by norm_num)
  apply hconv.congr
  intro t ht
  have hw := (fiber_root_line_piece_curvature id ht).1
  have hat : alpha - beta * t < 1 := by linarith only [hw]
  exact (fiber_profile_D_line_normal hr.ne' hm0.ne' hs.ne' hb0.ne' hat).symm

theorem fiber_profile_E_piece_convex (id : FiberRootLineIdentity) {u : ℝ}
    (hu : 0 ≤ u) (huhi : u ≤ 7 / 25) :
    ConvexOn ℝ (Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi))
      (fun t => fiberProfileE t u (lowMeanFractionReal (fiberRootLineById id).alpha -
        lowMeanFractionReal (fiberRootLineById id).beta * t)) := by
  let alpha := lowMeanFractionReal (fiberRootLineById id).alpha
  let beta := lowMeanFractionReal (fiberRootLineById id).beta
  have hp := fiber_root_line_parameters id
  have ha : 1 < alpha := hp.2.2.2.2.1
  have hb : 1 ≤ beta := hp.2.2.2.2.2.1
  have hb0 : 0 < beta := by linarith only [hb]
  have hconv : ConvexOn ℝ (Icc (lowMeanFractionReal (fiberRootLineById id).lo)
      (lowMeanFractionReal (fiberRootLineById id).hi))
      (fiberProfileLine (beta * fiberProfileEB0 u - 9 / 2 - 38 * u ^ 2)
        (-(alpha + 1) * fiberProfileEB0 u + 9 - 3 * u ^ 2)
        (fiberProfileEB0 u / beta - 9 / 2) ((alpha - 1) * fiberProfileEB0 u / beta)
        0 beta (alpha - 1)) := by
    apply fiber_profile_line_convex
    · intro t ht
      exact (fiber_root_line_piece_curvature id ht).1
    · intro t ht
      have hg := fiber_root_line_piece_curvature id ht
      exact (fiber_profile_E_second_strict ha hb hu huhi hg.1 hg.2).le
        |>.trans' (by norm_num)
  apply hconv.congr
  intro t ht
  have hw := (fiber_root_line_piece_curvature id ht).1
  have hat : alpha - beta * t < 1 := by linarith only [hw]
  exact (fiber_profile_E_line_normal hb0.ne' hat).symm

end Erdos993Lean.Analytic.V213
