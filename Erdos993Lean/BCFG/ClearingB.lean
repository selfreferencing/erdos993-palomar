module

public import Erdos993Lean.BCFG.ClearingProofCore
public import Erdos993Lean.BCFG.Generated.BHeavyB0.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BHeavyB3.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BHeavyH1.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BHeavyH2.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BLightCurvature.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BLightLeft.IntegerGuards
public import Erdos993Lean.BCFG.Generated.BLightRight.IntegerGuards

/-! Seven exact Eq.(15) identities for the original row B data.
No positivity theorem, numerical evaluation, coefficient truncation or
assumed analytic identity is used to prove an equality. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic
open CertData

theorem clearing_B_H0 {lam v : ℝ} (h : FunctionDomain .B .H0 lam v) :
    analyticFunction .B .H0 lam v = (BHeavyB0.clearingScale : ℝ) *
      clearingFactor .H0 lam * Bi.evalReal BHeavyB0.p lam v /
      clearingDenominator .B .H0 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  conv_rhs => rw [BHeavyB0.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BHeavyB0.pInt scale BHeavyB0.clearingScale order lam v

theorem clearing_B_H3 {lam v : ℝ} (h : FunctionDomain .B .H3 lam v) :
    analyticFunction .B .H3 lam v = (BHeavyB3.clearingScale : ℝ) *
      clearingFactor .H3 lam * Bi.evalReal BHeavyB3.p lam v /
      clearingDenominator .B .H3 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  conv_rhs => rw [BHeavyB3.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BHeavyB3.pInt scale BHeavyB3.clearingScale order lam v

theorem clearing_B_H1 {lam v : ℝ} (h : FunctionDomain .B .H1 lam v) :
    analyticFunction .B .H1 lam v = (BHeavyH1.clearingScale : ℝ) *
      clearingFactor .H1 lam * Bi.evalReal BHeavyH1.p lam v /
      clearingDenominator .B .H1 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  conv_rhs => rw [BHeavyH1.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BHeavyH1.pInt scale BHeavyH1.clearingScale order lam v

theorem clearing_B_H2 {lam v : ℝ} (h : FunctionDomain .B .H2 lam v) :
    analyticFunction .B .H2 lam v = (BHeavyH2.clearingScale : ℝ) *
      clearingFactor .H2 lam * Bi.evalReal BHeavyH2.p lam v /
      clearingDenominator .B .H2 lam v := by
  obtain ⟨hl,hv,hL,hV,hA,hE,hZ⟩ := heavy_clearing_facts h
  simp only [heavyExponent] at hA hE
  apply clearing_eq_of_cross h
  conv_rhs => rw [BHeavyH2.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BHeavyH2.pInt scale BHeavyH2.clearingScale order lam v

theorem clearing_B_J {lam x : ℝ} (h : FunctionDomain .B .J lam x) :
    analyticFunction .B .J lam x = (BLightCurvature.clearingScale : ℝ) *
      clearingFactor .J lam * Bi.evalReal BLightCurvature.p lam x /
      clearingDenominator .B .J lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  conv_rhs => rw [BLightCurvature.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BLightCurvature.pInt scale BLightCurvature.clearingScale order lam x

theorem clearing_B_C0 {lam x : ℝ} (h : FunctionDomain .B .C0 lam x) :
    analyticFunction .B .C0 lam x = (BLightLeft.clearingScale : ℝ) *
      clearingFactor .C0 lam * Bi.evalReal BLightLeft.p lam x /
      clearingDenominator .B .C0 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  conv_rhs => rw [BLightLeft.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BLightLeft.pInt scale BLightLeft.clearingScale order lam x cancel

theorem clearing_B_C1 {lam x : ℝ} (h : FunctionDomain .B .C1 lam x) :
    analyticFunction .B .C1 lam x = (BLightRight.clearingScale : ℝ) *
      clearingFactor .C1 lam * Bi.evalReal BLightRight.p lam x /
      clearingDenominator .B .C1 lam x := by
  obtain ⟨hl,hL,hB,hC,hA,hE,hw,hZ⟩ := light_clearing_facts h
  apply clearing_eq_of_cross h
  conv_rhs => rw [BLightRight.integer_source_p, ← integerBiValue_eq_cast_eval]
  bcfg_exact_clear BLightRight.pInt scale BLightRight.clearingScale order lam x cancel

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.clearing_B_H0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_H0
#check Erdos993Lean.BCFG.Analytic.clearing_B_H3
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_H3
#check Erdos993Lean.BCFG.Analytic.clearing_B_H1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_H1
#check Erdos993Lean.BCFG.Analytic.clearing_B_H2
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_H2
#check Erdos993Lean.BCFG.Analytic.clearing_B_J
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_J
#check Erdos993Lean.BCFG.Analytic.clearing_B_C0
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_C0
#check Erdos993Lean.BCFG.Analytic.clearing_B_C1
#print axioms Erdos993Lean.BCFG.Analytic.clearing_B_C1
#check Erdos993Lean.BCFG.CertData.BHeavyB0.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BHeavyB0.integer_source_p
#check Erdos993Lean.BCFG.CertData.BHeavyB3.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BHeavyB3.integer_source_p
#check Erdos993Lean.BCFG.CertData.BHeavyH1.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BHeavyH1.integer_source_p
#check Erdos993Lean.BCFG.CertData.BHeavyH2.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BHeavyH2.integer_source_p
#check Erdos993Lean.BCFG.CertData.BLightCurvature.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BLightCurvature.integer_source_p
#check Erdos993Lean.BCFG.CertData.BLightLeft.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BLightLeft.integer_source_p
#check Erdos993Lean.BCFG.CertData.BLightRight.integer_source_p
#print axioms Erdos993Lean.BCFG.CertData.BLightRight.integer_source_p
