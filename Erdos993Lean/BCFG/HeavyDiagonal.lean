module

public import Erdos993Lean.BCFG.DiagonalContinuity
public import Erdos993Lean.BCFG.HeavyBase
public import Erdos993Lean.BCFG.ChartPathGeometry
public import Erdos993Lean.BCFG.ChartDeterminantPositivity
public import Erdos993Lean.BCFG.MatrixBridge

/-! The heavy diagonal stays positive along the fixed-rho path from
v=1/2. All path, continuity and determinant premises are discharged here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set

theorem heavyUpper_nonneg_onDomain {r : AnalyticRow} {lam v : ℝ}
    (h : HeavyDomain r lam v) : 0 ≤ heavyUpper r lam v := by
  have hl := activity_pos h.1
  have hv : 0 < v := by linarith [h.2.1]
  have hw := heavyOmega_pos (r := r) hl hv
  have hw1 := heavyOmega_lt_one_onDomain h
  have hY : 0 ≤ logMass (heavyOmega r lam v) :=
    neg_nonneg.mpr (Real.log_nonpos hw.le hw1.le)
  exact hY.trans (heavy_logMass_bounds h).2

theorem heavy_diagonal_continuousOn {r : AnalyticRow} {lam v rho : ℝ}
    (h : HeavyDomain r lam v) :
    ContinuousOn (fun w => rCoeff r lam (heavyOmega r lam w)-
      tailP r lam (heavyOmega r lam w) rho*heavyUpper r lam w) (Icc (1/2) v) := by
  intro w hw
  have hwpos : 0 < w := by linarith [hw.1]
  exact (chart_diagonal_continuousAt (activity_pos h.1)
    (heavyOmega_pos (r := r) (activity_pos h.1) hwpos)
    (heavyOmega_continuousAt r lam w) continuousAt_const
    (heavyUpper_continuousAt hw.1 (hw.2.trans h.2.2))).continuousWithinAt

/-- Actual feasible heavy-chart diagonal sign, including both v endpoints. -/
theorem heavy_diagonal_pos {r : AnalyticRow} {lam v rho : ℝ}
    (h : HeavyDomain r lam v) (hlo : rhoZero lam (heavyOmega r lam v) ≤ rho)
    (hhi : rho ≤ 1) :
    0 < rCoeff r lam (heavyOmega r lam v)-
      tailP r lam (heavyOmega r lam v) rho*heavyUpper r lam v := by
  have hl := activity_pos h.1
  have hv : 0 < v := by linarith [h.2.1]
  have hr0 : 0 ≤ rho := ((rhoZero_bounds hl (heavyOmega_pos (r := r) hl hv)).1.trans_le hlo).le
  have hbase := heavy_base_diagonal_pos h.1 hr0 hhi
  have hcont := heavy_diagonal_continuousOn (rho := rho) h
  apply continuous_positive_of_nonzero hcont hbase ?_ v ⟨h.2.1,le_rfl⟩
  intro w hw
  obtain ⟨hdomain,_,_,_,hwrho,_⟩ := heavy_feasible_along_path h hw.1 hw.2 hlo hhi
  have hD := heavy_determinant_pos hdomain hwrho hhi
  rw [heavyDeterminant_eq] at hD
  exact diagonal_ne_zero_of_scaled_det (heavyUpper_nonneg_onDomain hdomain) hD

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavyUpper_nonneg_onDomain
#print axioms Erdos993Lean.BCFG.Analytic.heavyUpper_nonneg_onDomain
#check Erdos993Lean.BCFG.Analytic.heavy_diagonal_continuousOn
#print axioms Erdos993Lean.BCFG.Analytic.heavy_diagonal_continuousOn
#check Erdos993Lean.BCFG.Analytic.heavy_diagonal_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavy_diagonal_pos
