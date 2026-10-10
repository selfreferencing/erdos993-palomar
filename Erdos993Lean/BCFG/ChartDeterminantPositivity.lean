module

public import Erdos993Lean.BCFG.AnalyticPositivity
public import Erdos993Lean.BCFG.DeterminantPositivity
public import Erdos993Lean.BCFG.LightSource
public import Erdos993Lean.BCFG.ChartGeometry

/-! Determinant signs on the actual closed charts and feasible rho interval.
All previously explicit analytic-function and leading-coefficient signs are
discharged from original domains; no final free sign premise remains. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

/-- The original feasible rho interval has an exact normalized vacancy coordinate. -/
theorem vacancy_normalization {rho0 rho : ℝ}
    (h0 : rho0 < 1) (hlo : rho0 ≤ rho) (hhi : rho ≤ 1) :
    0 ≤ (rho-rho0)/(1-rho0) ∧ (rho-rho0)/(1-rho0) ≤ 1 ∧
      rho0+(1-rho0)*((rho-rho0)/(1-rho0)) = rho := by
  have hd : 0 < 1-rho0 := sub_pos.mpr h0
  refine ⟨div_nonneg (sub_nonneg.mpr hlo) hd.le,
    (div_le_one hd).2 (by linarith only [hhi]),?_⟩
  field_simp [hd.ne'] <;> ring

theorem light_cubic_leading_nonpos_onDomain {r : AnalyticRow} {lam x : ℝ}
    (h : LightDomain r lam x) : lightCoefficient r lam x 3 ≤ 0 := by
  have hl := activity_pos h.1
  have hw := lightOmega_pos hl h.2.1 h.2.2
  have hbounds := lightOmega_bounds hl h.2.1 h.2.2
  exact light_cubic_leading_nonpos (rhoZero_bounds hl hw).2.le
    (lightUpper_nonneg hl h.2.1 h.2.2) (dCoeff_pos hl hw).le
    (price_pos (r := r) hl).le (lightSourceA_pos hl hbounds.1).le

theorem heavy_determinant_pos_normalized {r : AnalyticRow} {lam v t : ℝ}
    (h : HeavyDomain r lam v) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < heavyDeterminant r lam v
      (rhoZero lam (heavyOmega r lam v)+(1-rhoZero lam (heavyOmega r lam v))*t) := by
  exact heavy_determinant_pos_of_functions (analyticFunction_pos (f := .H0) h)
    (analyticFunction_pos (f := .H1) h) (analyticFunction_pos (f := .H2) h)
    (analyticFunction_pos (f := .H3) h) ht0 ht1

theorem light_determinant_pos_normalized {r : AnalyticRow} {lam x t : ℝ}
    (h : LightDomain r lam x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lightDeterminant r lam x
      (rhoZero lam (lightOmega lam x)+(1-rhoZero lam (lightOmega lam x))*t) := by
  exact light_determinant_pos_of_functions (analyticFunction_pos (f := .J) h)
    (analyticFunction_pos (f := .C0) h) (analyticFunction_pos (f := .C1) h)
    (light_cubic_leading_nonpos_onDomain h) ht0 ht1

/-- Actual heavy determinant sign; only chart and original feasible-rho hypotheses. -/
theorem heavy_determinant_pos {r : AnalyticRow} {lam v rho : ℝ}
    (h : HeavyDomain r lam v) (hlo : rhoZero lam (heavyOmega r lam v) ≤ rho)
    (hhi : rho ≤ 1) : 0 < heavyDeterminant r lam v rho := by
  have hl := activity_pos h.1
  have hhalf : (0 : ℝ) < 1/2 := div_pos zero_lt_one
    (by exact_mod_cast (by decide +kernel : 0 < (2 : ℕ)))
  have hv : 0 < v := hhalf.trans_le h.2.1
  have hw := heavyOmega_pos (r := r) hl hv
  obtain ⟨ht0,ht1,hid⟩ := vacancy_normalization (rhoZero_bounds hl hw).2 hlo hhi
  have hd := heavy_determinant_pos_normalized h ht0 ht1
  rw [hid] at hd
  exact hd

/-- Actual light determinant sign, including x=0; no artificial nonleaf restriction. -/
theorem light_determinant_pos {r : AnalyticRow} {lam x rho : ℝ}
    (h : LightDomain r lam x) (hlo : rhoZero lam (lightOmega lam x) ≤ rho)
    (hhi : rho ≤ 1) : 0 < lightDeterminant r lam x rho := by
  have hl := activity_pos h.1
  have hw := lightOmega_pos hl h.2.1 h.2.2
  obtain ⟨ht0,ht1,hid⟩ := vacancy_normalization (rhoZero_bounds hl hw).2 hlo hhi
  have hd := light_determinant_pos_normalized h ht0 ht1
  rw [hid] at hd
  exact hd

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.vacancy_normalization
#print axioms Erdos993Lean.BCFG.Analytic.vacancy_normalization
#check Erdos993Lean.BCFG.Analytic.light_cubic_leading_nonpos_onDomain
#print axioms Erdos993Lean.BCFG.Analytic.light_cubic_leading_nonpos_onDomain
#check Erdos993Lean.BCFG.Analytic.heavy_determinant_pos_normalized
#print axioms Erdos993Lean.BCFG.Analytic.heavy_determinant_pos_normalized
#check Erdos993Lean.BCFG.Analytic.light_determinant_pos_normalized
#print axioms Erdos993Lean.BCFG.Analytic.light_determinant_pos_normalized
#check Erdos993Lean.BCFG.Analytic.heavy_determinant_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavy_determinant_pos
#check Erdos993Lean.BCFG.Analytic.light_determinant_pos
#print axioms Erdos993Lean.BCFG.Analytic.light_determinant_pos
