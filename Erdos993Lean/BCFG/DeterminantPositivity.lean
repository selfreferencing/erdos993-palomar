module

public import Erdos993Lean.BCFG.AnalyticDecompositions

/-! Algebraic sign transport for the exact T6b cubic identities.
Analytic-function positivity and the light cubic sign are explicit premises
of these intermediate lemmas, to be discharged before any transfer theorem. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem heavy_decomposition_pos {H0 H1 H2 H3 t : ℝ}
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2) (h3 : 0 < H3)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < H0*(1-t)*(1-2*t)^2+3*H1*t*(1-t)^2+
      3*H2*t^2*(1-t)+H3*t^3 := by
  by_cases hz : t = 0
  · simpa [hz] using h0
  by_cases ho : t = 1
  · simpa [ho] using h3
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
  have hu : 0 < 1-t := sub_pos.mpr (lt_of_le_of_ne ht1 ho)
  have ha : 0 ≤ H0*(1-t)*(1-2*t)^2 := by positivity
  have hb : 0 < 3*H1*t*(1-t)^2 := by positivity
  have hc : 0 ≤ 3*H2*t^2*(1-t) := by positivity
  have hd : 0 ≤ H3*t^3 := by positivity
  linarith

theorem light_decomposition_pos {J C0 C1 a3 u t : ℝ}
    (hJ : 0 < J) (h0 : 0 < C0) (h1 : 0 < C1) (ha3 : a3 ≤ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < (J-a3*(1-t))*(t-u)^2+C0*(1-t)+C1*t := by
  have hx : a3*(1-t) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg ha3 (by linarith)
  have hcoeff : 0 < J-a3*(1-t) := by linarith
  have hs : 0 ≤ (J-a3*(1-t))*(t-u)^2 := mul_nonneg hcoeff.le (sq_nonneg _)
  by_cases ho : t = 1
  · simp only [ho, sub_self, mul_zero, zero_add, mul_one]
    exact add_pos_of_nonneg_of_pos (by positivity) h1
  · have hu : 0 < 1-t := sub_pos.mpr (lt_of_le_of_ne ht1 ho)
    have hl : 0 < C0*(1-t) := mul_pos h0 hu
    have hr : 0 ≤ C1*t := mul_nonneg h1.le ht0
    linarith

theorem heavy_determinant_pos_of_functions {r : AnalyticRow} {lam v t : ℝ}
    (h0 : 0 < analyticFunction r .H0 lam v)
    (h1 : 0 < analyticFunction r .H1 lam v)
    (h2 : 0 < analyticFunction r .H2 lam v)
    (h3 : 0 < analyticFunction r .H3 lam v)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < heavyDeterminant r lam v
      (rhoZero lam (heavyOmega r lam v)+(1-rhoZero lam (heavyOmega r lam v))*t) := by
  rw [heavy_determinant_decomposition]
  exact heavy_decomposition_pos h0 h1 h2 h3 ht0 ht1

theorem light_determinant_pos_of_functions {r : AnalyticRow} {lam x t : ℝ}
    (hJ : 0 < analyticFunction r .J lam x)
    (h0 : 0 < analyticFunction r .C0 lam x)
    (h1 : 0 < analyticFunction r .C1 lam x)
    (ha3 : lightCoefficient r lam x 3 ≤ 0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < lightDeterminant r lam x
      (rhoZero lam (lightOmega lam x)+(1-rhoZero lam (lightOmega lam x))*t) := by
  rw [light_determinant_decomposition]
  exact light_decomposition_pos hJ h0 h1 ha3 ht0 ht1

theorem light_cubic_leading_coefficient (r : AnalyticRow) (lam x : ℝ) :
    lightCoefficient r lam x 3 =
      -(1-rhoZero lam (lightOmega lam x))^3*lightUpper lam x*
        dCoeff lam (lightOmega lam x)*price r lam*
          lightSourceA lam (lightOmega lam x) := by
  norm_num [lightCoefficient, vacancyCoefficient, Finset.sum_range_succ,
    lightRawCoefficient, rawCoefficient, lightK2]
  ring

theorem light_cubic_leading_nonpos {r : AnalyticRow} {lam x : ℝ}
    (hrho : rhoZero lam (lightOmega lam x) ≤ 1)
    (hU : 0 ≤ lightUpper lam x) (hd : 0 ≤ dCoeff lam (lightOmega lam x))
    (hp : 0 ≤ price r lam) (ha : 0 ≤ lightSourceA lam (lightOmega lam x)) :
    lightCoefficient r lam x 3 ≤ 0 := by
  rw [light_cubic_leading_coefficient]
  have hprod : 0 ≤ (1-rhoZero lam (lightOmega lam x))^3*lightUpper lam x*
      dCoeff lam (lightOmega lam x)*price r lam*
        lightSourceA lam (lightOmega lam x) := by positivity
  nlinarith

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavy_decomposition_pos
#print axioms Erdos993Lean.BCFG.Analytic.heavy_decomposition_pos
#check Erdos993Lean.BCFG.Analytic.light_decomposition_pos
#print axioms Erdos993Lean.BCFG.Analytic.light_decomposition_pos
#check Erdos993Lean.BCFG.Analytic.heavy_determinant_pos_of_functions
#print axioms Erdos993Lean.BCFG.Analytic.heavy_determinant_pos_of_functions
#check Erdos993Lean.BCFG.Analytic.light_determinant_pos_of_functions
#print axioms Erdos993Lean.BCFG.Analytic.light_determinant_pos_of_functions
#check Erdos993Lean.BCFG.Analytic.light_cubic_leading_coefficient
#print axioms Erdos993Lean.BCFG.Analytic.light_cubic_leading_coefficient
#check Erdos993Lean.BCFG.Analytic.light_cubic_leading_nonpos
#print axioms Erdos993Lean.BCFG.Analytic.light_cubic_leading_nonpos
