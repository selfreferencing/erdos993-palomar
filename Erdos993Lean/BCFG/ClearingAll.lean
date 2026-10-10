module
public import Erdos993Lean.BCFG.ClearingB
public import Erdos993Lean.BCFG.ClearingC
public import Erdos993Lean.BCFG.ClearingF
public import Erdos993Lean.BCFG.ClearingG

/-! Named all-28 interface for Eq.(15). The scale selector aliases the original
data constants verbatim. It does not re-encode a coefficient or scale array. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Erdos993Lean.BCFG.Analytic
open CertData

def originalClearingScale : AnalyticRow → DeterminantFunction → ℚ
  | .B, .H0 => BHeavyB0.clearingScale
  | .B, .H3 => BHeavyB3.clearingScale
  | .B, .H1 => BHeavyH1.clearingScale
  | .B, .H2 => BHeavyH2.clearingScale
  | .B, .J => BLightCurvature.clearingScale
  | .B, .C0 => BLightLeft.clearingScale
  | .B, .C1 => BLightRight.clearingScale
  | .C, .H0 => CHeavyB0.clearingScale
  | .C, .H3 => CHeavyB3.clearingScale
  | .C, .H1 => CHeavyH1.clearingScale
  | .C, .H2 => CHeavyH2.clearingScale
  | .C, .J => CLightCurvature.clearingScale
  | .C, .C0 => CLightLeft.clearingScale
  | .C, .C1 => CLightRight.clearingScale
  | .F, .H0 => FHeavyB0.clearingScale
  | .F, .H3 => FHeavyB3.clearingScale
  | .F, .H1 => FHeavyH1.clearingScale
  | .F, .H2 => FHeavyH2.clearingScale
  | .F, .J => FLightCurvature.clearingScale
  | .F, .C0 => FLightLeft.clearingScale
  | .F, .C1 => FLightRight.clearingScale
  | .G, .H0 => GHeavyB0.clearingScale
  | .G, .H3 => GHeavyB3.clearingScale
  | .G, .H1 => GHeavyH1.clearingScale
  | .G, .H2 => GHeavyH2.clearingScale
  | .G, .J => GLightCurvature.clearingScale
  | .G, .C0 => GLightLeft.clearingScale
  | .G, .C1 => GLightRight.clearingScale

theorem analyticFunction_eq_originalPolynomial (r : AnalyticRow)
    (f : DeterminantFunction) {lam y : ℝ} (h : FunctionDomain r f lam y) :
    analyticFunction r f lam y = (originalClearingScale r f : ℝ) *
      clearingFactor f lam * Bi.evalReal (Packet.data (analyticPolynomialId r f)).p lam y /
      clearingDenominator r f lam y := by
  cases r with
  | B =>
      cases f with
      | H0 => exact clearing_B_H0 h
      | H3 => exact clearing_B_H3 h
      | H1 => exact clearing_B_H1 h
      | H2 => exact clearing_B_H2 h
      | J => exact clearing_B_J h
      | C0 => exact clearing_B_C0 h
      | C1 => exact clearing_B_C1 h
  | C =>
      cases f with
      | H0 => exact clearing_C_H0 h
      | H3 => exact clearing_C_H3 h
      | H1 => exact clearing_C_H1 h
      | H2 => exact clearing_C_H2 h
      | J => exact clearing_C_J h
      | C0 => exact clearing_C_C0 h
      | C1 => exact clearing_C_C1 h
  | F =>
      cases f with
      | H0 => exact clearing_F_H0 h
      | H3 => exact clearing_F_H3 h
      | H1 => exact clearing_F_H1 h
      | H2 => exact clearing_F_H2 h
      | J => exact clearing_F_J h
      | C0 => exact clearing_F_C0 h
      | C1 => exact clearing_F_C1 h
  | G =>
      cases f with
      | H0 => exact clearing_G_H0 h
      | H3 => exact clearing_G_H3 h
      | H1 => exact clearing_G_H1 h
      | H2 => exact clearing_G_H2 h
      | J => exact clearing_G_J h
      | C0 => exact clearing_G_C0 h
      | C1 => exact clearing_G_C1 h

end Erdos993Lean.BCFG.Analytic
#check Erdos993Lean.BCFG.Analytic.originalClearingScale
#print axioms Erdos993Lean.BCFG.Analytic.originalClearingScale
#check Erdos993Lean.BCFG.Analytic.analyticFunction_eq_originalPolynomial
#print axioms Erdos993Lean.BCFG.Analytic.analyticFunction_eq_originalPolynomial
