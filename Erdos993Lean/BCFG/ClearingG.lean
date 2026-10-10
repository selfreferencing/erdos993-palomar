module
public import Erdos993Lean.BCFG.ClearingProofCore
public import Erdos993Lean.BCFG.Generated.GHeavyB0.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GHeavyB3.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GHeavyH1.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GHeavyH2.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GLightCurvature.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GLightLeft.IntegerGuards
public import Erdos993Lean.BCFG.Generated.GLightRight.IntegerGuards
public import Erdos993Lean.BCFG.ClearingF

/-! Exact Eq.(15), row G. Original arrays/scales are imported unchanged. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Erdos993Lean.BCFG.Analytic
open CertData

theorem clearing_G_H0 {lam v : ℝ} (h : FunctionDomain .G .H0 lam v) :
    analyticFunction .G .H0 lam v = (GHeavyB0.clearingScale : ℝ) *
      clearingFactor .H0 lam * Bi.evalReal GHeavyB0.p lam v /
      clearingDenominator .G .H0 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [GHeavyB0.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear GHeavyB0.pInt scale GHeavyB0.clearingScale order lam v

theorem clearing_G_H3 {lam v : ℝ} (h : FunctionDomain .G .H3 lam v) :
    analyticFunction .G .H3 lam v = (GHeavyB3.clearingScale : ℝ) *
      clearingFactor .H3 lam * Bi.evalReal GHeavyB3.p lam v /
      clearingDenominator .G .H3 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [GHeavyB3.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear GHeavyB3.pInt scale GHeavyB3.clearingScale order lam v

theorem clearing_G_H1 {lam v : ℝ} (h : FunctionDomain .G .H1 lam v) :
    analyticFunction .G .H1 lam v = (GHeavyH1.clearingScale : ℝ) *
      clearingFactor .H1 lam * Bi.evalReal GHeavyH1.p lam v /
      clearingDenominator .G .H1 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [GHeavyH1.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear GHeavyH1.pInt scale GHeavyH1.clearingScale order lam v

theorem clearing_G_H2 {lam v : ℝ} (h : FunctionDomain .G .H2 lam v) :
    analyticFunction .G .H2 lam v = (GHeavyH2.clearingScale : ℝ) *
      clearingFactor .H2 lam * Bi.evalReal GHeavyH2.p lam v /
      clearingDenominator .G .H2 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [GHeavyH2.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear GHeavyH2.pInt scale GHeavyH2.clearingScale order lam v

theorem clearing_G_J {lam x : ℝ} (h : FunctionDomain .G .J lam x) :
    analyticFunction .G .J lam x = (GLightCurvature.clearingScale : ℝ) *
      clearingFactor .J lam * Bi.evalReal GLightCurvature.p lam x /
      clearingDenominator .G .J lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [GLightCurvature.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear GLightCurvature.pInt scale GLightCurvature.clearingScale order lam x

theorem clearing_G_C0 {lam x : ℝ} (h : FunctionDomain .G .C0 lam x) :
    analyticFunction .G .C0 lam x = (GLightLeft.clearingScale : ℝ) *
      clearingFactor .C0 lam * Bi.evalReal GLightLeft.p lam x /
      clearingDenominator .G .C0 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [GLightLeft.integer_source_p, ← integerBiValue_eq_cast_eval]
  apply mul_left_cancel₀ (pow_ne_zero 2 hl.ne')
  bcfg_exact_clear GLightLeft.pInt scale GLightLeft.clearingScale order lam x

theorem clearing_G_C1 {lam x : ℝ} (h : FunctionDomain .G .C1 lam x) :
    analyticFunction .G .C1 lam x = (GLightRight.clearingScale : ℝ) *
      clearingFactor .C1 lam * Bi.evalReal GLightRight.p lam x /
      clearingDenominator .G .C1 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [GLightRight.integer_source_p, ← integerBiValue_eq_cast_eval]
  apply mul_left_cancel₀ (pow_ne_zero 2 hl.ne')
  bcfg_exact_clear GLightRight.pInt scale GLightRight.clearingScale order lam x

end Erdos993Lean.BCFG.Analytic
#check Erdos993Lean.BCFG.Analytic.clearing_G_H0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_H0
#check Erdos993Lean.BCFG.Analytic.clearing_G_H3
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_H3
#check Erdos993Lean.BCFG.Analytic.clearing_G_H1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_H1
#check Erdos993Lean.BCFG.Analytic.clearing_G_H2
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_H2
#check Erdos993Lean.BCFG.Analytic.clearing_G_J
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_J
#check Erdos993Lean.BCFG.Analytic.clearing_G_C0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_C0
#check Erdos993Lean.BCFG.Analytic.clearing_G_C1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_G_C1
#check Erdos993Lean.BCFG.CertData.GHeavyB0.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GHeavyB0.integer_source_p
#check Erdos993Lean.BCFG.CertData.GHeavyB3.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GHeavyB3.integer_source_p
#check Erdos993Lean.BCFG.CertData.GHeavyH1.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GHeavyH1.integer_source_p
#check Erdos993Lean.BCFG.CertData.GHeavyH2.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GHeavyH2.integer_source_p
#check Erdos993Lean.BCFG.CertData.GLightCurvature.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GLightCurvature.integer_source_p
#check Erdos993Lean.BCFG.CertData.GLightLeft.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GLightLeft.integer_source_p
#check Erdos993Lean.BCFG.CertData.GLightRight.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.GLightRight.integer_source_p
