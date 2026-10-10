module

public import Erdos993Lean.BCFG.MassLine
public import Erdos993Lean.BCFG.ChartGeometry
public import Erdos993Lean.Analytic.V213.ResponseRatioPolynomials

/-! Literal comparison choices used by the one-vertex reduction. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Erdos993Lean.Analytic
open Erdos993Lean.Analytic.V213.VarianceResponse

theorem reduction_cubic_bound {p : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) :
    messageRatio p ≤ cubicEnvelope p := by
  simpa only [cubicEnvelope, ratioT3] using messageRatio_le_T3 hp hp1

theorem reduction_source_nonneg {lam p rho : ℝ} (hl : 0 < lam)
    (hp : 0 ≤ p) (hrho : 0 ≤ rho) : 0 ≤ O2.src lam p rho := by
  exact (O2.fq_nonneg (O2.actQ_pos' hl) (mul_nonneg hp hrho)).trans
    (le_max_left _ _)

theorem reduction_cavity_identity {lam omega : ℝ} (hl : 0 < lam)
    (hw : 0 < omega) :
    O2.cavH lam (occupation lam omega) = min (q lam) (1-omega) := by
  simpa only [occupation, chartParent, q, actQ] using chart_cavity_cap hl hw

theorem reduction_massLine_cavity {r : AnalyticRow} {lam omega : ℝ}
    (hrow : InRow r lam) (hw : 0 < omega) (hw1 : omega ≤ 1) :
    massLine r lam ≤ messageRatio (O2.cavH lam (occupation lam omega)) := by
  have hl := activity_pos hrow
  have hq := q_bounds hl
  have hc0 : 0 ≤ O2.cavH lam (occupation lam omega) := by
    rw [reduction_cavity_identity hl hw]
    exact le_min hq.1.le (by linarith)
  have hcq : O2.cavH lam (occupation lam omega) ≤ q lam := by
    rw [reduction_cavity_identity hl hw]
    exact min_le_left _ _
  exact (massLine_le_messageRatio hrow).trans
    (messageRatio_antitoneOn ⟨hc0, hcq.trans_lt hq.2⟩ ⟨hq.1.le, hq.2⟩ hcq)

theorem reduction_rho_identity {lam omega : ℝ} (hl : 0 < lam)
    (hw : 0 < omega) :
    1/(1+lam*(1-occupation lam omega)) = rhoZero lam omega := by
  have hd : 1+lam*omega ≠ 0 := ne_of_gt (by positivity)
  unfold occupation rhoZero
  have hden : 1+lam*(1-lam*omega/(1+lam*omega)) =
      (1+lam+lam*omega)/(1+lam*omega) := by
    field_simp [hd]
    ring
  rw [hden, one_div, inv_div]

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.reduction_cubic_bound
#print axioms Erdos993Lean.BCFG.Analytic.reduction_cubic_bound
#check Erdos993Lean.BCFG.Analytic.reduction_source_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.reduction_source_nonneg
#check Erdos993Lean.BCFG.Analytic.reduction_cavity_identity
#print axioms Erdos993Lean.BCFG.Analytic.reduction_cavity_identity
#check Erdos993Lean.BCFG.Analytic.reduction_massLine_cavity
#print axioms Erdos993Lean.BCFG.Analytic.reduction_massLine_cavity
#check Erdos993Lean.BCFG.Analytic.reduction_rho_identity
#print axioms Erdos993Lean.BCFG.Analytic.reduction_rho_identity
