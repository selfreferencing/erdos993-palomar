module

public import Erdos993Lean.BCFG.ClearingEnvelopeForms
public import Erdos993Lean.BCFG.ClearingDenominators

/-! Canonical light-chart factors used before polynomial expansion. -/
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Erdos993Lean.BCFG.Analytic

theorem lightOmega_canonical {lam x : ℝ} (hL : 1+lam ≠ 0) :
    lightOmega lam x = lightB lam x/(1+lam) := by
  unfold lightOmega q lightB
  field_simp [hL]
  <;> ring

theorem lightSourceB_canonical {lam x : ℝ} (hl : lam ≠ 0) (hL : 1+lam ≠ 0) :
    lightSourceB lam (lightOmega lam x) = -(1-x)/(2*lam) := by
  rw [lightSourceB, lightOmega_canonical hL]
  unfold lightB
  field_simp [hl, hL]
  <;> ring

theorem lightSourceA_canonical {lam x : ℝ} (hl : lam ≠ 0)
    (hL : 1+lam ≠ 0) (hA : lightA lam x ≠ 0) :
    lightSourceA lam (lightOmega lam x) =
      (2*lam+1)*(lam*(2*lam+1)*lightB lam x+(lightB lam x)^2-(1+lam))/
        (4*lam^2*lightA lam x) := by
  rw [lightSourceA, lightOmega_canonical hL]
  have hden : 1+lam*(lightB lam x/(1+lam)) = lightA lam x/(1+lam) := by
    unfold lightA lightB
    field_simp [hL]
    <;> ring
  rw [hden]
  unfold lightB
  field_simp [hl, hL, hA]
  <;> ring

theorem lightUpper_canonical {lam x : ℝ} (hw : 0 < lightOmega lam x)
    (hL : 1+lam ≠ 0) (hB : lightB lam x ≠ 0) (hC : lightC lam x ≠ 0) :
    lightUpper lam x = lam*x*
      (3*(lightB lam x)^4+68*(lightB lam x)^3*(1+lam)+
        98*(lightB lam x)^2*(1+lam)^2+68*lightB lam x*(1+lam)^3+3*(1+lam)^4)/
      (30*(1+lam)*lightB lam x*(lightC lam x)^3) := by
  rw [lightUpper_closed_form lam x hw, lightOmega_canonical hL]
  have hden : 1+lightB lam x/(1+lam) = lightC lam x/(1+lam) := by
    unfold lightB lightC
    field_simp [hL]
    <;> ring
  rw [hden]
  field_simp [hL, hB, hC]
  unfold lightB
  ring

end Erdos993Lean.BCFG.Analytic
