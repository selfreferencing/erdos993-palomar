module

public import Erdos993Lean.BCFG.ActualReductionChoices
public import Erdos993Lean.BCFG.LightSource
public import Erdos993Lean.BCFG.LightMassClosed
public import Erdos993Lean.BCFG.TailRationalGates
public import Erdos993Lean.Analytic.V213.ResponseChartSource
public import Erdos993Lean.Analytic.V213.ResponseRatioBounds

/-! Literal source, mass and ratio choices for the original one-vertex lemma.
No analytic determinant or payment positivity is assumed here. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open Erdos993Lean.Analytic
open Erdos993Lean.Analytic.V213.VarianceResponse

/-- The heavy source bound is globally valid, by the first two max branches. -/
theorem heavy_source_minorant {lam p rho : ℝ} (hl : 0 < lam) :
    sourceA lam*p*rho ≤ O2.src lam p rho := by
  have ha : sourceSlopeA (actQ lam) = sourceA lam := by
    unfold sourceSlopeA sourceA actQ
    field_simp [hl.ne', (show 1+lam ≠ 0 by linarith)] <;> ring
  have hfirst : sourceSlopeA (actQ lam)*(p*rho) ≤ O2.fq (actQ lam) (p*rho) := by
    rw [fq_branches]
    exact le_max_left _ _
  rw [ha] at hfirst
  have hfirst' : sourceA lam*p*rho ≤ O2.fq (actQ lam) (p*rho) := by
    simpa only [mul_assoc] using hfirst
  exact hfirst'.trans (le_max_left _ _)

theorem reduction_massLine_pos {r : AnalyticRow} {lam : ℝ} (h : InRow r lam) :
    0 < massLine r lam := by
  have hBC : (0 : ℝ) < 3/4 :=
    tail_fraction_pos (by decide +kernel : 0 < (4 : ℕ))
      (by decide +kernel : 0*4 < (3 : ℕ)*1)
  have hFG : (0 : ℝ) < 5/8 :=
    tail_fraction_pos (by decide +kernel : 0 < (8 : ℕ))
      (by decide +kernel : 0*8 < (5 : ℕ)*1)
  have hm := massLine_strict_lower h
  cases r
  · exact hBC.trans (hm.1 (Or.inl rfl))
  · exact hBC.trans (hm.1 (Or.inr rfl))
  · exact hFG.trans (hm.2 (Or.inl rfl))
  · exact hFG.trans (hm.2 (Or.inr rfl))

theorem reduction_cavity_ratio_nonneg {lam omega : ℝ}
    (hl : 0 < lam) (hw : 0 < omega) (hw1 : omega ≤ 1) :
    0 ≤ messageRatio (O2.cavH lam (occupation lam omega)) := by
  have hq := q_bounds hl
  have hc0 : 0 ≤ O2.cavH lam (occupation lam omega) := by
    rw [reduction_cavity_identity hl hw]
    exact le_min hq.1.le (sub_nonneg.mpr hw1)
  have hcq : O2.cavH lam (occupation lam omega) ≤ q lam := by
    rw [reduction_cavity_identity hl hw]
    exact min_le_left _ _
  have hc1 := hcq.trans_lt hq.2
  exact (sub_pos.mpr hc1).le.trans (messageRatio_weak_bounds hc0 hc1).1

/-- On the full light chart the child cap is exactly 1-omega. -/
theorem light_cavity_exact {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    O2.cavH lam (occupation lam (lightOmega lam x)) = 1-lightOmega lam x := by
  have hw := lightOmega_pos hl hx0 hx1
  have hb := (lightOmega_bounds hl hx0 hx1).1
  have hid := one_sub_q lam (show 1+lam ≠ 0 by linarith)
  have hc : 1-lightOmega lam x ≤ q lam := by linarith
  rw [reduction_cavity_identity hl hw, min_eq_right hc]

/-- The light H0*Y binding is exact, including omega=1 and the assigned h(0). -/
theorem light_mass_choice_exact {lam x : ℝ} (hl : 0 < lam)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    messageRatio (O2.cavH lam (occupation lam (lightOmega lam x)))*
      logMass (lightOmega lam x) = 1-lightOmega lam x := by
  have hw := lightOmega_pos hl hx0 hx1
  have hw1 := (lightOmega_bounds hl hx0 hx1).2
  have hY : 0 ≤ logMass (lightOmega lam x) :=
    neg_nonneg.mpr (Real.log_nonpos hw.le hw1)
  have he : Real.exp (-logMass (lightOmega lam x)) = lightOmega lam x := by
    simp only [logMass, neg_neg, Real.exp_log hw]
  rw [light_cavity_exact hl hx0 hx1]
  have h := messageRatio_light_mass_nonneg hY
  rwa [he] at h

/-- The eta used in the matrix is exactly the eta in the original quadratic. -/
theorem reduction_eta_identity (r : AnalyticRow) (lam omega Y : ℝ) :
    rCoeff r lam omega/Y = gamma r lam/(occupation lam omega*Y) := by
  rw [rCoeff, div_div]

/-- The source comparison and exact light mass give literal equality of K. -/
theorem light_choice_K_exact {r : AnalyticRow} {lam x rho : ℝ}
    (hl : 0 < lam) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    price r lam*rho*(lightSourceA lam (lightOmega lam x)*rho+
      lightSourceB lam (lightOmega lam x))+alpha r*(1-rho)+
      beta r*rho*messageRatio (O2.cavH lam (occupation lam (lightOmega lam x)))*
        logMass (lightOmega lam x) = lightK r lam x rho := by
  rw [mul_assoc (beta r*rho), light_mass_choice_exact hl hx0 hx1]
  rfl

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavy_source_minorant
#print axioms Erdos993Lean.BCFG.Analytic.heavy_source_minorant
#check Erdos993Lean.BCFG.Analytic.reduction_massLine_pos
#print axioms Erdos993Lean.BCFG.Analytic.reduction_massLine_pos
#check Erdos993Lean.BCFG.Analytic.reduction_cavity_ratio_nonneg
#print axioms Erdos993Lean.BCFG.Analytic.reduction_cavity_ratio_nonneg
#check Erdos993Lean.BCFG.Analytic.light_cavity_exact
#print axioms Erdos993Lean.BCFG.Analytic.light_cavity_exact
#check Erdos993Lean.BCFG.Analytic.light_mass_choice_exact
#print axioms Erdos993Lean.BCFG.Analytic.light_mass_choice_exact
#check Erdos993Lean.BCFG.Analytic.reduction_eta_identity
#print axioms Erdos993Lean.BCFG.Analytic.reduction_eta_identity
#check Erdos993Lean.BCFG.Analytic.light_choice_K_exact
#print axioms Erdos993Lean.BCFG.Analytic.light_choice_K_exact
