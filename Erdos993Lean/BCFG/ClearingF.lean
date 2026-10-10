module
public import Erdos993Lean.BCFG.ClearingProofCore
public import Erdos993Lean.BCFG.Generated.FHeavyB0.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FHeavyB3.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FHeavyH1.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FHeavyH2.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FLightCurvature.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FLightLeft.IntegerGuards
public import Erdos993Lean.BCFG.Generated.FLightRight.IntegerGuards
public import Erdos993Lean.BCFG.ClearingC

/-! Exact Eq.(15), row F. Original arrays/scales are imported unchanged. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Erdos993Lean.BCFG.Analytic
open CertData

theorem clearing_F_H0 {lam v : ℝ} (h : FunctionDomain .F .H0 lam v) :
    analyticFunction .F .H0 lam v = (FHeavyB0.clearingScale : ℝ) *
      clearingFactor .H0 lam * Bi.evalReal FHeavyB0.p lam v /
      clearingDenominator .F .H0 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [FHeavyB0.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear FHeavyB0.pInt scale FHeavyB0.clearingScale order lam v

theorem clearing_F_H3 {lam v : ℝ} (h : FunctionDomain .F .H3 lam v) :
    analyticFunction .F .H3 lam v = (FHeavyB3.clearingScale : ℝ) *
      clearingFactor .H3 lam * Bi.evalReal FHeavyB3.p lam v /
      clearingDenominator .F .H3 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [FHeavyB3.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear FHeavyB3.pInt scale FHeavyB3.clearingScale order lam v

theorem clearing_F_H1 {lam v : ℝ} (h : FunctionDomain .F .H1 lam v) :
    analyticFunction .F .H1 lam v = (FHeavyH1.clearingScale : ℝ) *
      clearingFactor .H1 lam * Bi.evalReal FHeavyH1.p lam v /
      clearingDenominator .F .H1 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [FHeavyH1.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear FHeavyH1.pInt scale FHeavyH1.clearingScale order lam v

theorem clearing_F_H2 {lam v : ℝ} (h : FunctionDomain .F .H2 lam v) :
    analyticFunction .F .H2 lam v = (FHeavyH2.clearingScale : ℝ) *
      clearingFactor .H2 lam * Bi.evalReal FHeavyH2.p lam v /
      clearingDenominator .F .H2 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [FHeavyH2.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear FHeavyH2.pInt scale FHeavyH2.clearingScale order lam v

theorem clearing_F_J {lam x : ℝ} (h : FunctionDomain .F .J lam x) :
    analyticFunction .F .J lam x = (FLightCurvature.clearingScale : ℝ) *
      clearingFactor .J lam * Bi.evalReal FLightCurvature.p lam x /
      clearingDenominator .F .J lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [FLightCurvature.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear FLightCurvature.pInt scale FLightCurvature.clearingScale order lam x

theorem clearing_F_C0 {lam x : ℝ} (h : FunctionDomain .F .C0 lam x) :
    analyticFunction .F .C0 lam x = (FLightLeft.clearingScale : ℝ) *
      clearingFactor .C0 lam * Bi.evalReal FLightLeft.p lam x /
      clearingDenominator .F .C0 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [FLightLeft.integer_source_p, ← integerBiValue_eq_cast_eval]
  apply mul_left_cancel₀ (pow_ne_zero 2 hl.ne')
  bcfg_exact_clear FLightLeft.pInt scale FLightLeft.clearingScale order lam x

theorem clearing_F_C1 {lam x : ℝ} (h : FunctionDomain .F .C1 lam x) :
    analyticFunction .F .C1 lam x = (FLightRight.clearingScale : ℝ) *
      clearingFactor .C1 lam * Bi.evalReal FLightRight.p lam x /
      clearingDenominator .F .C1 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [FLightRight.integer_source_p, ← integerBiValue_eq_cast_eval]
  apply mul_left_cancel₀ (pow_ne_zero 2 hl.ne')
  bcfg_exact_clear FLightRight.pInt scale FLightRight.clearingScale order lam x

end Erdos993Lean.BCFG.Analytic
#check Erdos993Lean.BCFG.Analytic.clearing_F_H0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_H0
#check Erdos993Lean.BCFG.Analytic.clearing_F_H3
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_H3
#check Erdos993Lean.BCFG.Analytic.clearing_F_H1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_H1
#check Erdos993Lean.BCFG.Analytic.clearing_F_H2
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_H2
#check Erdos993Lean.BCFG.Analytic.clearing_F_J
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_J
#check Erdos993Lean.BCFG.Analytic.clearing_F_C0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_C0
#check Erdos993Lean.BCFG.Analytic.clearing_F_C1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_F_C1
#check Erdos993Lean.BCFG.CertData.FHeavyB0.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FHeavyB0.integer_source_p
#check Erdos993Lean.BCFG.CertData.FHeavyB3.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FHeavyB3.integer_source_p
#check Erdos993Lean.BCFG.CertData.FHeavyH1.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FHeavyH1.integer_source_p
#check Erdos993Lean.BCFG.CertData.FHeavyH2.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FHeavyH2.integer_source_p
#check Erdos993Lean.BCFG.CertData.FLightCurvature.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FLightCurvature.integer_source_p
#check Erdos993Lean.BCFG.CertData.FLightLeft.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FLightLeft.integer_source_p
#check Erdos993Lean.BCFG.CertData.FLightRight.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.FLightRight.integer_source_p
