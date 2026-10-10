module

public import Erdos993Lean.BCFG.PaymentChoices
public import Erdos993Lean.BCFG.ChartLogEnvelopes
public import Erdos993Lean.BCFG.HeavyDiagonal
public import Erdos993Lean.BCFG.LightDiagonal

/-! Scalar payment margins on the original heavy and light chart domains.
The diagonal signs come from the separately authored named continuity theorem;
the determinant signs come from the original integer packets and exact clearing.
No free analytic positivity premise remains in a chart margin. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Erdos993Lean.Analytic
open Erdos993Lean.Analytic.V213.VarianceResponse

theorem chart_oneVertexPsi_identity
    (r : AnalyticRow) (lam omega rho z f0 H0 : ℝ) :
    oneVertexPsi (price r lam) (alpha r) (beta r) (gamma r lam)
      (occupation lam omega) rho (logMass omega) z f0 H0
      (cubicEnvelope (occupation lam omega)) =
    (price r lam*rho*f0+alpha r*(1-rho)+beta r*rho*H0*logMass omega)-
      tailP r lam omega rho+2*(tailP r lam omega rho-centerResponse r)*(1-z)+
      (rCoeff r lam omega/logMass omega-tailP r lam omega rho)*(1-z)^2 := by
  simp only [oneVertexPsi, tailP, eCoeff, dCoeff, centerResponse, rCoeff, div_div]
  ring

theorem heavy_choice_K_lower {r : AnalyticRow} {lam v rho : ℝ}
    (h : HeavyDomain r lam v) (hrho : 0 ≤ rho) :
    heavyK r lam v rho ≤
      price r lam*rho*(sourceA lam*occupation lam (heavyOmega r lam v)*rho)+
        alpha r*(1-rho)+beta r*rho*massLine r lam*logMass (heavyOmega r lam v) := by
  have hm : 0 ≤ beta r*rho*massLine r lam :=
    mul_nonneg (mul_nonneg (row_constants_pos r).2.2.1.le hrho)
      (reduction_massLine_pos h.1).le
  have hlower := mul_le_mul_of_nonneg_left (heavy_logMass_bounds h).1 hm
  unfold heavyK
  nlinarith only [hlower]

/-- All real signed responses are allowed in the heavy scalar comparison. -/
theorem heavy_chart_psi {r : AnalyticRow} {lam v rho : ℝ}
    (h : HeavyDomain r lam v) (hlo : rhoZero lam (heavyOmega r lam v) ≤ rho)
    (hhi : rho ≤ 1) (z : ℝ) :
    epsilon < oneVertexPsi (price r lam) (alpha r) (beta r) (gamma r lam)
      (occupation lam (heavyOmega r lam v)) rho (logMass (heavyOmega r lam v)) z
      (sourceA lam*occupation lam (heavyOmega r lam v)*rho) (massLine r lam)
      (cubicEnvelope (occupation lam (heavyOmega r lam v))) := by
  have hl := activity_pos h.1
  have hv : 0 < v := by linarith [h.2.1]
  have hw := heavyOmega_pos (r := r) hl hv
  have hrho := (rhoZero_bounds hl hw).1.le.trans hlo
  have hY : 0 < logMass (heavyOmega r lam v) :=
    neg_pos.mpr (Real.log_neg hw (heavyOmega_lt_one_onDomain h))
  have hD := heavy_determinant_pos h hlo hhi
  rw [heavyDeterminant_eq] at hD
  have hC := heavy_diagonal_pos h hlo hhi
  have hm := all_response_minorant (heavy_choice_K_lower h hrho) hY
    (heavy_logMass_bounds h).2 (rCoeff_pos (r := r) hl hw).le hC hD z
  rw [chart_oneVertexPsi_identity]
  exact hm

/-- The nonleaf light scalar comparison, retaining only its positive mass domain. -/
theorem light_chart_psi {r : AnalyticRow} {lam x rho : ℝ}
    (h : LightDomain r lam x) (hlo : rhoZero lam (lightOmega lam x) ≤ rho)
    (hhi : rho ≤ 1) (hY : 0 < logMass (lightOmega lam x)) (z : ℝ) :
    epsilon < oneVertexPsi (price r lam) (alpha r) (beta r) (gamma r lam)
      (occupation lam (lightOmega lam x)) rho (logMass (lightOmega lam x)) z
      (lightSourceA lam (lightOmega lam x)*rho+lightSourceB lam (lightOmega lam x))
      (messageRatio (O2.cavH lam (occupation lam (lightOmega lam x))))
      (cubicEnvelope (occupation lam (lightOmega lam x))) := by
  have hl := activity_pos h.1
  have hw := lightOmega_pos hl h.2.1 h.2.2
  have hK := (light_choice_K_exact (r := r) (rho := rho) hl h.2.1 h.2.2).ge
  have hD := light_determinant_pos h hlo hhi
  rw [lightDeterminant_eq] at hD
  have hC := light_diagonal_pos h hlo hhi
  have hm := all_response_minorant hK hY (light_logMass_bounds h).2
    (rCoeff_pos (r := r) hl hw).le hC hD z
  rw [chart_oneVertexPsi_identity]
  exact hm

/-- At x=0 the regular scaled determinant gives the leaf margin without 1/Y. -/
theorem light_leaf_scalar {r : AnalyticRow} {lam rho : ℝ}
    (hrow : InRow r lam) (hlo : rhoZero lam 1 ≤ rho) (hhi : rho ≤ 1) :
    epsilon < lightK r lam 0 rho-tailP r lam 1 rho := by
  have hl := activity_pos hrow
  have hlight : LightDomain r lam 0 := ⟨hrow, le_rfl, zero_le_one⟩
  have hlo' : rhoZero lam (lightOmega lam 0) ≤ rho := by
    simpa only [(light_log_zero lam).1] using hlo
  have hD := light_determinant_pos hlight hlo' hhi
  rw [lightDeterminant_eq, (light_log_zero lam).1, (light_log_zero lam).2.2] at hD
  simp only [mul_zero, sub_zero, zero_mul] at hD
  exact leaf_margin_of_scaled_det le_rfl (rCoeff_pos (r := r) hl zero_lt_one) hD

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.chart_oneVertexPsi_identity
#print axioms Erdos993Lean.BCFG.Analytic.chart_oneVertexPsi_identity
#check Erdos993Lean.BCFG.Analytic.heavy_choice_K_lower
#print axioms Erdos993Lean.BCFG.Analytic.heavy_choice_K_lower
#check Erdos993Lean.BCFG.Analytic.heavy_chart_psi
#print axioms Erdos993Lean.BCFG.Analytic.heavy_chart_psi
#check Erdos993Lean.BCFG.Analytic.light_chart_psi
#print axioms Erdos993Lean.BCFG.Analytic.light_chart_psi
#check Erdos993Lean.BCFG.Analytic.light_leaf_scalar
#print axioms Erdos993Lean.BCFG.Analytic.light_leaf_scalar
