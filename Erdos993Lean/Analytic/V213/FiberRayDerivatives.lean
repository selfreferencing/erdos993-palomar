module

public import Erdos993Lean.Analytic.V213.FiberRayCoefficients

/-!
Actual pre-cap and rho-star derivatives in Eq93.
Generic derivative proofs are adapted from an earlier development.

Original old finite-check imports and endpoint
certificate premises are not used. These names retain the actual
current E2 and beta formulas; regional derivative guards are proved later.
-/

@[expose] public section
namespace Erdos993Lean.Analytic.V213
open Erdos993Lean.Analytic.V22 Erdos993Lean.Analytic.V22.Analysis

theorem fiberRayCalc_activity_denominator_pos {rm : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 < 1 - rm^2 := by
  nlinarith [mul_nonneg hrm (sub_nonneg.mpr hrmhi)]

theorem fiberRayCalc_cCoef_pos {N : ℝ} (hN : 1 < N) : 0 < cCoef N := by
  have hrecip : (1 : ℝ)/N < 1 := (div_lt_one (by linarith)).mpr hN
  dsimp [cCoef]
  linarith

theorem fiberRayCalc_e4_eq_e5 {rm N : ℝ} (hN : 0 < N) (hd : 1-rm^2 ≠ 0) :
    e4 N rm = e5 rm + e5 rm/N := by
  dsimp [e4, e5]
  field_simp [ne_of_gt hN, hd] <;> ring

/-- Exact derivative of `c=1-1/N`. -/
theorem fiberRayCalc_cCoef_hasDerivAt {N : ℝ} (hN : 0 < N) :
    HasDerivAt cCoef (1/N^2) N := by
  convert (hasDerivAt_const N (1 : ℝ)).sub
    ((hasDerivAt_const N (1 : ℝ)).div (hasDerivAt_id N) (ne_of_gt hN)) using 1
  · funext z
    rfl
  · simp only [id_eq]
    ring

theorem fiberRayCalc_rho_hasDerivAt {N : ℝ} (hN : 0 < N) :
    HasDerivAt rho (1/(N+1)^2) N := by
  convert (hasDerivAt_id N).div ((hasDerivAt_id N).add_const 1)
    (show N+1 ≠ 0 from ne_of_gt (by linarith)) using 1
  · funext z
    dsimp [rho] <;> ring
  · dsimp
    ring

/-- A positive derivative formula for the actual retained `ρ_*`. -/
noncomputable def fiberRayCalc_rhoStarDerivative (rm N : ℝ) : ℝ :=
  let cD := (1/N^2)/(2*Real.sqrt (cCoef N))
  (1-rm^2)/(N+1)^2
    + 2*(Real.sqrt (cCoef N)+(N+1)*cD)/((N+1)*Real.sqrt (cCoef N))^2
    + rm^2*(3*(1-rm^2)*cD)/(3*(1-rm^2)*Real.sqrt (cCoef N))^2

theorem fiberRayCalc_rhoStar_hasDerivAt {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N) :
    HasDerivAt (fun n => rhoStar n rm) (fiberRayCalc_rhoStarDerivative rm N) N := by
  have hd := fiberRayCalc_activity_denominator_pos hrm hrmhi
  have hc := fiberRayCalc_cCoef_pos hN
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  have hsder := (fiberRayCalc_cCoef_hasDerivAt (show 0 < N by linarith)).sqrt (ne_of_gt hc)
  have hden1 := ((hasDerivAt_id N).add_const 1).mul hsder
  have hden2 := hsder.const_mul (3*(1-rm^2))
  have hterm1 := (fiberRayCalc_rho_hasDerivAt (show 0 < N by linarith)).const_mul (1-rm^2)
  have hterm2 := (hasDerivAt_const N (2 : ℝ)).div hden1
    (ne_of_gt (mul_pos (show 0 < N+1 by linarith) hs))
  have hterm3 := (hasDerivAt_const N (rm^2)).div hden2
    (ne_of_gt (mul_pos (mul_pos (by norm_num) hd) hs))
  convert (hterm1.sub hterm2).sub hterm3 using 1
  · funext z
    dsimp [rhoStar] <;> ring
  · dsimp [fiberRayCalc_rhoStarDerivative]
    ring

theorem fiberRayCalc_rhoStarDerivative_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N) :
    0 ≤ fiberRayCalc_rhoStarDerivative rm N := by
  have hd := fiberRayCalc_activity_denominator_pos hrm hrmhi
  have hc := fiberRayCalc_cCoef_pos hN
  have hs : 0 < Real.sqrt (cCoef N) := Real.sqrt_pos.mpr hc
  have hn : 0 < N+1 := by linarith
  dsimp [fiberRayCalc_rhoStarDerivative]
  positivity

/-- An algebraically identical pre-cap expression, with the cancelled
`e₄(N) r_m² N` written so its derivative is transparent. -/
noncomputable def fiberRayCalc_preCapE2 (rm N : ℝ) : ℝ :=
  e2 + e3 rm*rm*Real.sqrt N + e5 rm*rm^2*(N+1)
    + e5 rm*rm^3*(Real.sqrt N)^3

noncomputable def fiberRayCalc_preCapE2Derivative (rm N : ℝ) : ℝ :=
  e3 rm*rm/(2*Real.sqrt N) + e5 rm*rm^2
    + (3/2)*e5 rm*rm^3*Real.sqrt N

theorem fiberRayCalc_preCapE2_eq {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) :
    fiberRayCalc_preCapE2 rm N = fiberRayE2 N rm (rm*Real.sqrt N) := by
  have hd := ne_of_gt (fiberRayCalc_activity_denominator_pos hrm hrmhi)
  dsimp [fiberRayCalc_preCapE2, fiberRayE2]
  rw [fiberRayCalc_e4_eq_e5 hN hd]
  simp only [mul_pow, Real.sq_sqrt hN.le]
  field_simp [ne_of_gt hN] <;> ring

theorem fiberRayCalc_preCapE2_hasDerivAt {rm N : ℝ} (hN : 0 < N) :
    HasDerivAt (fiberRayCalc_preCapE2 rm) (fiberRayCalc_preCapE2Derivative rm N) N := by
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hN)
  have hspos : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have h := (((hasDerivAt_const N e2).add (hs.const_mul (e3 rm*rm))).add
    (((hasDerivAt_id N).add_const 1).const_mul (e5 rm*rm^2))).add
    ((hs.pow 3).const_mul (e5 rm*rm^3))
  convert h using 1
  · funext z
    dsimp [fiberRayCalc_preCapE2] <;> ring
  · dsimp [fiberRayCalc_preCapE2Derivative] <;>
    norm_num <;> field_simp [ne_of_gt hspos] <;> ring

theorem fiberRayCalc_preCapE2_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 0 < N) :
    0 ≤ fiberRayCalc_preCapE2 rm N := by
  rw [fiberRayCalc_preCapE2_eq hrm hrmhi hN]
  exact fiber_ray_E2_nonneg hN hrm hrmhi (by positivity)

theorem fiberRayCalc_preCapE2Derivative_nonneg {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) : 0 ≤ fiberRayCalc_preCapE2Derivative rm N := by
  have hd := fiberRayCalc_activity_denominator_pos hrm hrmhi
  have he3 : 0 ≤ e3 rm := by unfold e3; positivity
  have he5 : 0 ≤ e5 rm := by unfold e5; positivity
  dsimp [fiberRayCalc_preCapE2Derivative]
  positivity

noncomputable def fiberRayCalc_preCapBeta (rm N : ℝ) : ℝ := N-1-2/rhoStar N rm*fiberRayCalc_preCapE2 rm N

noncomputable def fiberRayCalc_preCapBetaDerivative (rm N : ℝ) : ℝ :=
  1-2/rhoStar N rm*fiberRayCalc_preCapE2Derivative rm N
    + 2*fiberRayCalc_preCapE2 rm N*fiberRayCalc_rhoStarDerivative rm N/(rhoStar N rm)^2

theorem fiberRayCalc_preCapBeta_hasDerivAt {rm N : ℝ}
    (hrm : 0 ≤ rm) (hrmhi : rm ≤ 1/2) (hN : 1 < N)
    (hrs : 0 < rhoStar N rm) :
    HasDerivAt (fiberRayCalc_preCapBeta rm) (fiberRayCalc_preCapBetaDerivative rm N) N := by
  have hquot := (hasDerivAt_const N (2 : ℝ)).div
    (fiberRayCalc_rhoStar_hasDerivAt hrm hrmhi hN) (ne_of_gt hrs)
  have hprod := hquot.mul (fiberRayCalc_preCapE2_hasDerivAt (rm := rm) (show 0 < N by linarith))
  convert ((hasDerivAt_id N).sub_const 1).sub hprod using 1
  · funext z
    dsimp [fiberRayCalc_preCapBeta] <;> ring
  · dsimp [fiberRayCalc_preCapBetaDerivative]
    field_simp [ne_of_gt hrs] <;> ring


end Erdos993Lean.Analytic.V213
