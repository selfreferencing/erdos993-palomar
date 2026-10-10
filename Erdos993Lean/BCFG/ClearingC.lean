module
public import Erdos993Lean.BCFG.ClearingProofCore
public import Erdos993Lean.BCFG.Generated.CHeavyB0.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CHeavyB3.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CHeavyH1.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CHeavyH2.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CLightCurvature.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CLightLeft.IntegerGuards
public import Erdos993Lean.BCFG.Generated.CLightRight.IntegerGuards
public import Erdos993Lean.BCFG.ClearingB

/-! Exact Eq.(15), row C. Original arrays/scales are imported unchanged. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Erdos993Lean.BCFG.Analytic
open CertData

theorem clearing_C_H0 {lam v : ℝ} (h : FunctionDomain .C .H0 lam v) :
    analyticFunction .C .H0 lam v = (CHeavyB0.clearingScale : ℝ) *
      clearingFactor .H0 lam * Bi.evalReal CHeavyB0.p lam v /
      clearingDenominator .C .H0 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [CHeavyB0.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CHeavyB0.pInt scale CHeavyB0.clearingScale order lam v

theorem clearing_C_H3 {lam v : ℝ} (h : FunctionDomain .C .H3 lam v) :
    analyticFunction .C .H3 lam v = (CHeavyB3.clearingScale : ℝ) *
      clearingFactor .H3 lam * Bi.evalReal CHeavyB3.p lam v /
      clearingDenominator .C .H3 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [CHeavyB3.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CHeavyB3.pInt scale CHeavyB3.clearingScale order lam v

theorem clearing_C_H1 {lam v : ℝ} (h : FunctionDomain .C .H1 lam v) :
    analyticFunction .C .H1 lam v = (CHeavyH1.clearingScale : ℝ) *
      clearingFactor .H1 lam * Bi.evalReal CHeavyH1.p lam v /
      clearingDenominator .C .H1 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [CHeavyH1.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CHeavyH1.pInt scale CHeavyH1.clearingScale order lam v

theorem clearing_C_H2 {lam v : ℝ} (h : FunctionDomain .C .H2 lam v) :
    analyticFunction .C .H2 lam v = (CHeavyH2.clearingScale : ℝ) *
      clearingFactor .H2 lam * Bi.evalReal CHeavyH2.p lam v /
      clearingDenominator .C .H2 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  rw [CHeavyH2.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CHeavyH2.pInt scale CHeavyH2.clearingScale order lam v

theorem clearing_C_J {lam x : ℝ} (h : FunctionDomain .C .J lam x) :
    analyticFunction .C .J lam x = (CLightCurvature.clearingScale : ℝ) *
      clearingFactor .J lam * Bi.evalReal CLightCurvature.p lam x /
      clearingDenominator .C .J lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [CLightCurvature.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CLightCurvature.pInt scale CLightCurvature.clearingScale order lam x

theorem clearing_C_C0 {lam x : ℝ} (h : FunctionDomain .C .C0 lam x) :
    analyticFunction .C .C0 lam x = (CLightLeft.clearingScale : ℝ) *
      clearingFactor .C0 lam * Bi.evalReal CLightLeft.p lam x /
      clearingDenominator .C .C0 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [CLightLeft.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CLightLeft.pInt scale CLightLeft.clearingScale order lam x cancel

theorem clearing_C_C1 {lam x : ℝ} (h : FunctionDomain .C .C1 lam x) :
    analyticFunction .C .C1 lam x = (CLightRight.clearingScale : ℝ) *
      clearingFactor .C1 lam * Bi.evalReal CLightRight.p lam x /
      clearingDenominator .C .C1 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  rw [CLightRight.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear CLightRight.pInt scale CLightRight.clearingScale order lam x cancel

end Erdos993Lean.BCFG.Analytic
#check Erdos993Lean.BCFG.Analytic.clearing_C_H0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_H0
#check Erdos993Lean.BCFG.Analytic.clearing_C_H3
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_H3
#check Erdos993Lean.BCFG.Analytic.clearing_C_H1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_H1
#check Erdos993Lean.BCFG.Analytic.clearing_C_H2
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_H2
#check Erdos993Lean.BCFG.Analytic.clearing_C_J
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_J
#check Erdos993Lean.BCFG.Analytic.clearing_C_C0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_C0
#check Erdos993Lean.BCFG.Analytic.clearing_C_C1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_C_C1
#check Erdos993Lean.BCFG.CertData.CHeavyB0.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CHeavyB0.integer_source_p
#check Erdos993Lean.BCFG.CertData.CHeavyB3.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CHeavyB3.integer_source_p
#check Erdos993Lean.BCFG.CertData.CHeavyH1.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CHeavyH1.integer_source_p
#check Erdos993Lean.BCFG.CertData.CHeavyH2.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CHeavyH2.integer_source_p
#check Erdos993Lean.BCFG.CertData.CLightCurvature.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CLightCurvature.integer_source_p
#check Erdos993Lean.BCFG.CertData.CLightLeft.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CLightLeft.integer_source_p
#check Erdos993Lean.BCFG.CertData.CLightRight.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.CLightRight.integer_source_p
