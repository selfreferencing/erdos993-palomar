module

public import Erdos993Lean.BCFG.ClearingAll
public import Erdos993Lean.BCFG.WholePacket

/-! Exact finite-to-analytic sign transport for all 28 actual functions.
Original packet arrays, scale constants and positivity theorems are reused.
No analytic-function sign or polynomial sign is assumed in the final theorem. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

open CertData

theorem originalClearingScale_pos (r : AnalyticRow) (f : DeterminantFunction) :
    0 < originalClearingScale r f := by
  cases r with
  | B =>
      cases f with
      | H0 => exact BHeavyB0.clearing_scale_positive
      | H3 => exact BHeavyB3.clearing_scale_positive
      | H1 => exact BHeavyH1.clearing_scale_positive
      | H2 => exact BHeavyH2.clearing_scale_positive
      | J => exact BLightCurvature.clearing_scale_positive
      | C0 => exact BLightLeft.clearing_scale_positive
      | C1 => exact BLightRight.clearing_scale_positive
  | C =>
      cases f with
      | H0 => exact CHeavyB0.clearing_scale_positive
      | H3 => exact CHeavyB3.clearing_scale_positive
      | H1 => exact CHeavyH1.clearing_scale_positive
      | H2 => exact CHeavyH2.clearing_scale_positive
      | J => exact CLightCurvature.clearing_scale_positive
      | C0 => exact CLightLeft.clearing_scale_positive
      | C1 => exact CLightRight.clearing_scale_positive
  | F =>
      cases f with
      | H0 => exact FHeavyB0.clearing_scale_positive
      | H3 => exact FHeavyB3.clearing_scale_positive
      | H1 => exact FHeavyH1.clearing_scale_positive
      | H2 => exact FHeavyH2.clearing_scale_positive
      | J => exact FLightCurvature.clearing_scale_positive
      | C0 => exact FLightLeft.clearing_scale_positive
      | C1 => exact FLightRight.clearing_scale_positive
  | G =>
      cases f with
      | H0 => exact GHeavyB0.clearing_scale_positive
      | H3 => exact GHeavyB3.clearing_scale_positive
      | H1 => exact GHeavyH1.clearing_scale_positive
      | H2 => exact GHeavyH2.clearing_scale_positive
      | J => exact GLightCurvature.clearing_scale_positive
      | C0 => exact GLightLeft.clearing_scale_positive
      | C1 => exact GLightRight.clearing_scale_positive

theorem originalClearingScale_cast_pos (r : AnalyticRow) (f : DeterminantFunction) :
    (0 : ℝ) < (originalClearingScale r f : ℝ) := by
  exact_mod_cast originalClearingScale_pos r f

/-- Original analytic domains equal the exact fixed packet's two closed intervals. -/
theorem functionDomain_iff_originalPacket (r : AnalyticRow) (f : DeterminantFunction)
    (lam y : ℝ) : FunctionDomain r f lam y ↔
      (((Packet.data (analyticPolynomialId r f)).l : ℝ) ≤ lam ∧
        lam ≤ ((Packet.data (analyticPolynomialId r f)).h : ℝ)) ∧
      (((Packet.data (analyticPolynomialId r f)).a : ℝ) ≤ y ∧
        y ≤ ((Packet.data (analyticPolynomialId r f)).a : ℝ)+
          ((Packet.data (analyticPolynomialId r f)).b : ℝ)) := by
  cases r <;> cases f <;>
    norm_num [FunctionDomain,HeavyDomain,LightDomain,InRow,rowLow,rowHigh,
      analyticPolynomialId,Packet.data,
      BHeavyB0.l,BHeavyB0.h,BHeavyB0.a,BHeavyB0.b,
      BHeavyB3.l,BHeavyB3.h,BHeavyB3.a,BHeavyB3.b,
      BHeavyH1.l,BHeavyH1.h,BHeavyH1.a,BHeavyH1.b,
      BHeavyH2.l,BHeavyH2.h,BHeavyH2.a,BHeavyH2.b,
      BLightCurvature.l,BLightCurvature.h,BLightCurvature.a,BLightCurvature.b,
      BLightLeft.l,BLightLeft.h,BLightLeft.a,BLightLeft.b,
      BLightRight.l,BLightRight.h,BLightRight.a,BLightRight.b,
      CHeavyB0.l,CHeavyB0.h,CHeavyB0.a,CHeavyB0.b,
      CHeavyB3.l,CHeavyB3.h,CHeavyB3.a,CHeavyB3.b,
      CHeavyH1.l,CHeavyH1.h,CHeavyH1.a,CHeavyH1.b,
      CHeavyH2.l,CHeavyH2.h,CHeavyH2.a,CHeavyH2.b,
      CLightCurvature.l,CLightCurvature.h,CLightCurvature.a,CLightCurvature.b,
      CLightLeft.l,CLightLeft.h,CLightLeft.a,CLightLeft.b,
      CLightRight.l,CLightRight.h,CLightRight.a,CLightRight.b,
      FHeavyB0.l,FHeavyB0.h,FHeavyB0.a,FHeavyB0.b,
      FHeavyB3.l,FHeavyB3.h,FHeavyB3.a,FHeavyB3.b,
      FHeavyH1.l,FHeavyH1.h,FHeavyH1.a,FHeavyH1.b,
      FHeavyH2.l,FHeavyH2.h,FHeavyH2.a,FHeavyH2.b,
      FLightCurvature.l,FLightCurvature.h,FLightCurvature.a,FLightCurvature.b,
      FLightLeft.l,FLightLeft.h,FLightLeft.a,FLightLeft.b,
      FLightRight.l,FLightRight.h,FLightRight.a,FLightRight.b,
      GHeavyB0.l,GHeavyB0.h,GHeavyB0.a,GHeavyB0.b,
      GHeavyB3.l,GHeavyB3.h,GHeavyB3.a,GHeavyB3.b,
      GHeavyH1.l,GHeavyH1.h,GHeavyH1.a,GHeavyH1.b,
      GHeavyH2.l,GHeavyH2.h,GHeavyH2.a,GHeavyH2.b,
      GLightCurvature.l,GLightCurvature.h,GLightCurvature.a,GLightCurvature.b,
      GLightLeft.l,GLightLeft.h,GLightLeft.a,GLightLeft.b,
      GLightRight.l,GLightRight.h,GLightRight.a,GLightRight.b]

theorem originalPolynomial_pos {r : AnalyticRow} {f : DeterminantFunction}
    {lam y : ℝ} (h : FunctionDomain r f lam y) :
    0 < Bi.evalReal (Packet.data (analyticPolynomialId r f)).p lam y := by
  have hpacket := (functionDomain_iff_originalPacket r f lam y).mp h
  exact Packet.all_whole_polynomials_positive (analyticPolynomialId r f)
    hpacket.1 hpacket.2

/-- Actual positivity for every row/function, with only its original closed domain. -/
theorem analyticFunction_pos {r : AnalyticRow} {f : DeterminantFunction}
    {lam y : ℝ} (h : FunctionDomain r f lam y) :
    0 < analyticFunction r f lam y := by
  rw [analyticFunction_eq_originalPolynomial r f h]
  exact div_pos
    (mul_pos (mul_pos (originalClearingScale_cast_pos r f) (clearingFactor_pos h))
      (originalPolynomial_pos h)) (clearingDenominator_pos h)

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.originalClearingScale_pos
#print axioms Erdos993Lean.BCFG.Analytic.originalClearingScale_pos
#check Erdos993Lean.BCFG.Analytic.originalClearingScale_cast_pos
#print axioms Erdos993Lean.BCFG.Analytic.originalClearingScale_cast_pos
#check Erdos993Lean.BCFG.Analytic.functionDomain_iff_originalPacket
#print axioms Erdos993Lean.BCFG.Analytic.functionDomain_iff_originalPacket
#check Erdos993Lean.BCFG.Analytic.originalPolynomial_pos
#print axioms Erdos993Lean.BCFG.Analytic.originalPolynomial_pos
#check Erdos993Lean.BCFG.Analytic.analyticFunction_pos
#print axioms Erdos993Lean.BCFG.Analytic.analyticFunction_pos

#check Erdos993Lean.BCFG.Packet.all_whole_polynomials_positive
#print axioms Erdos993Lean.BCFG.Packet.all_whole_polynomials_positive
#check Erdos993Lean.BCFG.CertData.BHeavyB0.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BHeavyB0.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BHeavyB3.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BHeavyB3.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BHeavyH1.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BHeavyH1.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BHeavyH2.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BHeavyH2.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BLightCurvature.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BLightCurvature.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BLightLeft.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BLightLeft.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.BLightRight.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.BLightRight.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CHeavyB0.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CHeavyB0.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CHeavyB3.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CHeavyB3.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CHeavyH1.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CHeavyH1.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CHeavyH2.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CHeavyH2.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CLightCurvature.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CLightCurvature.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CLightLeft.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CLightLeft.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.CLightRight.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.CLightRight.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FHeavyB0.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FHeavyB0.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FHeavyB3.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FHeavyB3.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FHeavyH1.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FHeavyH1.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FHeavyH2.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FHeavyH2.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FLightCurvature.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FLightCurvature.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FLightLeft.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FLightLeft.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.FLightRight.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.FLightRight.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GHeavyB0.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GHeavyB0.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GHeavyB3.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GHeavyB3.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GHeavyH1.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GHeavyH1.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GHeavyH2.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GHeavyH2.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GLightCurvature.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GLightCurvature.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GLightLeft.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GLightLeft.clearing_scale_positive
#check Erdos993Lean.BCFG.CertData.GLightRight.clearing_scale_positive
#print axioms Erdos993Lean.BCFG.CertData.GLightRight.clearing_scale_positive
