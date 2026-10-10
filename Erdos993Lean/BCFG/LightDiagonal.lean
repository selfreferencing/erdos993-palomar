module

public import Erdos993Lean.BCFG.DiagonalContinuity
public import Erdos993Lean.BCFG.ChartDeterminantPositivity
public import Erdos993Lean.BCFG.MatrixBridge
public import Erdos993Lean.BCFG.ChartLogEnvelopes

/-! The printed light path starts at x=0 with fixed normalized
vacancy t. At this endpoint U=0 and the diagonal is R>0. This proof does not
identify distinct heavy/light envelope formulas at their shared physical seam. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Set

def lightPathRho (lam t x : ℝ) : ℝ :=
  rhoZero lam (lightOmega lam x)+(1-rhoZero lam (lightOmega lam x))*t

theorem lightPathRho_continuousAt {lam t x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ContinuousAt (lightPathRho lam t) x := by
  have hc : ContinuousAt (fun y => rhoZero lam (lightOmega lam y)) x :=
    (rhoZero_continuousAt hl (lightOmega_pos hl hx0 hx1)).comp
      (lightOmega_continuousAt lam x)
  exact hc.add ((continuousAt_const.sub hc).mul continuousAt_const)

/-- Every point of the normalized closed light path satisfies original feasibility. -/
theorem lightPathRho_feasible {r : AnalyticRow} {lam x t : ℝ}
    (h : LightDomain r lam x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Feasible r lam (lightOmega lam x) (lightPathRho lam t x) := by
  have hl := activity_pos h.1
  have hw := lightOmega_pos hl h.2.1 h.2.2
  have hgap : 0 ≤ 1-rhoZero lam (lightOmega lam x) :=
    sub_nonneg.mpr (rhoZero_bounds hl hw).2.le
  have hlo := mul_nonneg hgap ht0
  have hhi := mul_le_mul_of_nonneg_left ht1 hgap
  refine ⟨h.1,hw,(lightOmega_bounds hl h.2.1 h.2.2).2,?_,?_⟩ <;>
    dsimp only [lightPathRho] <;> linarith

theorem light_diagonal_continuousOn {r : AnalyticRow} {lam t : ℝ}
    (hrow : InRow r lam) :
    ContinuousOn (fun x => rCoeff r lam (lightOmega lam x)-
      tailP r lam (lightOmega lam x) (lightPathRho lam t x)*lightUpper lam x) (Icc 0 1) := by
  intro x hx
  have hl := activity_pos hrow
  exact (chart_diagonal_continuousAt hl (lightOmega_pos hl hx.1 hx.2)
    (lightOmega_continuousAt lam x) (lightPathRho_continuousAt hl hx.1 hx.2)
    (lightUpper_continuousAt hl hx.1 hx.2)).continuousWithinAt

theorem light_diagonal_zero_pos {r : AnalyticRow} {lam rho : ℝ} (hrow : InRow r lam) :
    0 < rCoeff r lam (lightOmega lam 0)-
      tailP r lam (lightOmega lam 0) rho*lightUpper lam 0 := by
  have hw : 0 < lightOmega lam 0 := by simp [lightOmega]
  have hR := rCoeff_pos (r := r) (activity_pos hrow) hw
  simpa only [(light_log_zero lam).2.2,mul_zero,sub_zero] using hR

theorem light_diagonal_pos_normalized {r : AnalyticRow} {lam x t : ℝ}
    (h : LightDomain r lam x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < rCoeff r lam (lightOmega lam x)-
      tailP r lam (lightOmega lam x) (lightPathRho lam t x)*lightUpper lam x := by
  have hcont := light_diagonal_continuousOn (t := t) h.1
  have hbase := light_diagonal_zero_pos (rho := lightPathRho lam t 0) h.1
  apply continuous_positive_of_nonzero hcont hbase ?_ x h.2
  intro y hy
  have hdomain : LightDomain r lam y := ⟨h.1,hy⟩
  have hD := light_determinant_pos_normalized hdomain ht0 ht1
  change 0 < lightDeterminant r lam y (lightPathRho lam t y) at hD
  rw [lightDeterminant_eq] at hD
  exact diagonal_ne_zero_of_scaled_det
    (lightUpper_nonneg (activity_pos h.1) hy.1 hy.2) hD

/-- Actual feasible light-chart diagonal sign, including x=0 and x=1. -/
theorem light_diagonal_pos {r : AnalyticRow} {lam x rho : ℝ}
    (h : LightDomain r lam x) (hlo : rhoZero lam (lightOmega lam x) ≤ rho)
    (hhi : rho ≤ 1) :
    0 < rCoeff r lam (lightOmega lam x)-
      tailP r lam (lightOmega lam x) rho*lightUpper lam x := by
  have hl := activity_pos h.1
  have hw := lightOmega_pos hl h.2.1 h.2.2
  obtain ⟨ht0,ht1,hid⟩ := vacancy_normalization (rhoZero_bounds hl hw).2 hlo hhi
  have hc := light_diagonal_pos_normalized h ht0 ht1
  simpa only [lightPathRho,hid] using hc

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.lightPathRho
#print axioms Erdos993Lean.BCFG.Analytic.lightPathRho
#check Erdos993Lean.BCFG.Analytic.lightPathRho_continuousAt
#print axioms Erdos993Lean.BCFG.Analytic.lightPathRho_continuousAt
#check Erdos993Lean.BCFG.Analytic.lightPathRho_feasible
#print axioms Erdos993Lean.BCFG.Analytic.lightPathRho_feasible
#check Erdos993Lean.BCFG.Analytic.light_diagonal_continuousOn
#print axioms Erdos993Lean.BCFG.Analytic.light_diagonal_continuousOn
#check Erdos993Lean.BCFG.Analytic.light_diagonal_zero_pos
#print axioms Erdos993Lean.BCFG.Analytic.light_diagonal_zero_pos
#check Erdos993Lean.BCFG.Analytic.light_diagonal_pos_normalized
#print axioms Erdos993Lean.BCFG.Analytic.light_diagonal_pos_normalized
#check Erdos993Lean.BCFG.Analytic.light_diagonal_pos
#print axioms Erdos993Lean.BCFG.Analytic.light_diagonal_pos
