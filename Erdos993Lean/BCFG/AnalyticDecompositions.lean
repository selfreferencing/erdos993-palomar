module

public import Erdos993Lean.BCFG.ChartDefinitions

/-! Chart-specialized algebra. No positivity or clearing identity is assumed. -/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem heavyK_eq (r : AnalyticRow) (lam v rho : ℝ) :
    heavyK r lam v rho = alpha r+heavyK1 r lam v*rho+heavyK2 r lam v*rho^2 := by
  simp only [heavyK, heavyK1, heavyK2]
  ring

theorem lightK_eq (r : AnalyticRow) (lam x rho : ℝ) :
    lightK r lam x rho = alpha r+lightK1 r lam x*rho+lightK2 r lam x*rho^2 := by
  simp only [lightK, lightK1, lightK2]
  ring

/-- The heavy determinant is the printed scaled determinant with its actual K-minus. -/
theorem heavyDeterminant_eq (r : AnalyticRow) (lam v rho : ℝ) :
    heavyDeterminant r lam v rho =
      (heavyK r lam v rho-(eCoeff r lam (heavyOmega r lam v)+
        dCoeff lam (heavyOmega r lam v)*rho)-epsilon)*
        (rCoeff r lam (heavyOmega r lam v)-
          (eCoeff r lam (heavyOmega r lam v)+dCoeff lam (heavyOmega r lam v)*rho)*
            heavyUpper r lam v)-
        heavyUpper r lam v*(eCoeff r lam (heavyOmega r lam v)+
          dCoeff lam (heavyOmega r lam v)*rho-centerResponse r)^2 := by
  rw [heavyK_eq]
  rfl

/-- The light determinant retains its regular x=0 formula; no division by U is used. -/
theorem lightDeterminant_eq (r : AnalyticRow) (lam x rho : ℝ) :
    lightDeterminant r lam x rho =
      (lightK r lam x rho-(eCoeff r lam (lightOmega lam x)+
        dCoeff lam (lightOmega lam x)*rho)-epsilon)*
        (rCoeff r lam (lightOmega lam x)-
          (eCoeff r lam (lightOmega lam x)+dCoeff lam (lightOmega lam x)*rho)*
            lightUpper lam x)-
        lightUpper lam x*(eCoeff r lam (lightOmega lam x)+
          dCoeff lam (lightOmega lam x)*rho-centerResponse r)^2 := by
  rw [lightK_eq]
  rfl

/-- Eq.(11), with the four actual row-dependent analytic functions. -/
theorem heavy_determinant_decomposition (r : AnalyticRow) (lam v t : ℝ) :
    heavyDeterminant r lam v
      (rhoZero lam (heavyOmega r lam v)+(1-rhoZero lam (heavyOmega r lam v))*t) =
    analyticFunction r .H0 lam v*(1-t)*(1-2*t)^2+
      3*analyticFunction r .H1 lam v*t*(1-t)^2+
      3*analyticFunction r .H2 lam v*t^2*(1-t)+analyticFunction r .H3 lam v*t^3 := by
  calc
    _ = cubicValue (heavyCoefficient r lam v) t :=
      scaledDet_normalized (alpha r) epsilon (centerResponse r)
        (eCoeff r lam (heavyOmega r lam v)) (dCoeff lam (heavyOmega r lam v))
        (rCoeff r lam (heavyOmega r lam v)) (heavyUpper r lam v)
        (heavyK1 r lam v) (heavyK2 r lam v) (rhoZero lam (heavyOmega r lam v)) t
    _ = _ := by
      simpa only [analyticFunction, heavyBernstein] using
        heavy_cubic_identity (heavyCoefficient r lam v) t

/-- Eq.(14), with actual row-dependent center and analytic functions. -/
theorem light_determinant_decomposition (r : AnalyticRow) (lam x t : ℝ) :
    lightDeterminant r lam x
      (rhoZero lam (lightOmega lam x)+(1-rhoZero lam (lightOmega lam x))*t) =
    (analyticFunction r .J lam x-lightCoefficient r lam x 3*(1-t))*
      (t-lightCenter r x)^2+analyticFunction r .C0 lam x*(1-t)+
        analyticFunction r .C1 lam x*t := by
  calc
    _ = cubicValue (lightCoefficient r lam x) t :=
      scaledDet_normalized (alpha r) epsilon (centerResponse r)
        (eCoeff r lam (lightOmega lam x)) (dCoeff lam (lightOmega lam x))
        (rCoeff r lam (lightOmega lam x)) (lightUpper lam x)
        (lightK1 r lam x) (lightK2 r lam x) (rhoZero lam (lightOmega lam x)) t
    _ = _ := by
      simpa only [analyticFunction] using
        light_cubic_identity (lightCoefficient r lam x) (lightCenter r x) t

end Erdos993Lean.BCFG.Analytic

#check Erdos993Lean.BCFG.Analytic.heavyK_eq
#print axioms Erdos993Lean.BCFG.Analytic.heavyK_eq
#check Erdos993Lean.BCFG.Analytic.lightK_eq
#print axioms Erdos993Lean.BCFG.Analytic.lightK_eq
#check Erdos993Lean.BCFG.Analytic.heavyDeterminant_eq
#print axioms Erdos993Lean.BCFG.Analytic.heavyDeterminant_eq
#check Erdos993Lean.BCFG.Analytic.lightDeterminant_eq
#print axioms Erdos993Lean.BCFG.Analytic.lightDeterminant_eq
#check Erdos993Lean.BCFG.Analytic.heavy_determinant_decomposition
#print axioms Erdos993Lean.BCFG.Analytic.heavy_determinant_decomposition
#check Erdos993Lean.BCFG.Analytic.light_determinant_decomposition
#print axioms Erdos993Lean.BCFG.Analytic.light_determinant_decomposition
