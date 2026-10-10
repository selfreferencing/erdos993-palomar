module

public import F4Heavy.Analysis.HPrimaryCoordinates
public import F4Heavy.Analysis.HSupportCoordinates
public import F4Heavy.Analysis.DFGuardCore

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hFRadiusNum (v x zn T : ℝ) : ℝ :=
  let B := hBase v x
  let S := hVacancyDen v x
  let pn := hProbNum v x
  let Pn := hParentLowerNum v x
  let cn := pn*(2*Pn-(hAlphaNum v+hBetaNum v)*12*B^2*S)
  let dn := (hGammaNum v-hDeltaNum v)*12*(1-v)*B^3*S*T-pn*zn*Pn
  cn*(1-v)*T*hSupportDen v+2*dn*hVertexNum v 0

noncomputable def hFNum (v x zn T : ℝ) : ℝ :=
  let rn := hFRadiusNum v x zn T
  240*hDeltaNum v*(48*hProbNum v x*hBetaNum v*(1-v)^2*(hBase v x)^3*T*hSupportDen v+rn)*
    (1-v)*(hBase v x)^3*hVacancyDen v x*T*hSupportDen v-12*rn^2

noncomputable def hFDen (v x T : ℝ) : ℝ :=
  5*(12*(1-v)^2*(hBase v x)^3*hVacancyDen v x*T*hSupportDen v)^2

noncomputable def hFFormula (lam x z : ℝ) : ℝ :=
  let rho := dhVacancyX lam x
  let P := dhParentUpperX .H lam x rho
  let c := eProbabilityX lam x*(2*P-alpha .H lam-beta .H lam)
  let d := gamma .H lam-delta .H lam-eProbabilityX lam x*z*P
  let b := eProbabilityX lam x*beta .H lam*rho
  let r := c+2*d*hSupportVertex lam 0
  4*delta .H lam*(b+r)-(12/5)*r^2

theorem h_F_clear (dn pn bn rn q B S T H : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q)*(pn/B*(bn/q)*(4*q*B/S)+rn/(12*q^2*B^3*S*T*H))-
      (12/5)*(rn/(12*q^2*B^3*S*T*H))^2 =
      (240*dn*(48*pn*bn*q^2*B^3*T*H+rn)*q*B^3*S*T*H-12*rn^2)/
        (5*(12*q^2*B^3*S*T*H)^2) := by
  field_simp
  <;> ring

theorem h_F_formula_coordinate (v x z zn T : ℝ)
    (hq : 1-v ≠ 0) (hB : hBase v x ≠ 0) (hS : hVacancyDen v x ≠ 0)
    (hT : T ≠ 0) (hH : hSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    hFFormula (hActivity v) x z = hFNum v x zn T/hFDen v x T := by
  unfold hFFormula
  dsimp only
  rw [h_parent_lower_coordinate v x hq hB hS, h_probability_coordinate v x hq hB,
    h_alpha_coordinate v hq, h_beta_coordinate v hq, h_gamma_coordinate v hq,
    h_delta_coordinate v hq, h_vacancy_coordinate v x hq hB hS,
    h_lower_zero_vertex_coordinate v hq hH, hz]
  rw [dh_F_radius_clear _ _ _ _ _ _ _ _ _ _ _ _ _ hq hB hS hT hH]
  exact h_F_clear _ _ _ _ _ _ _ _ _ hq hB hS hT hH

end F4Heavy.Analysis
