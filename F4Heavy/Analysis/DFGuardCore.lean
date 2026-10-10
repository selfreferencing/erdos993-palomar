module

public import F4Heavy.Analysis.DZeroVertexCoordinate

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dFRadiusNum (v x zn T : ℝ) : ℝ :=
  let B := dBase v x
  let S := dVacancyDen v x
  let pn := dProbNum v x
  let Pn := dParentLowerNum v x
  let cn := pn*(2*Pn-(dAlphaNum v+dBetaNum v)*12*B^2*S)
  let dn := (dGammaNum v-dDeltaNum v)*12*(1-v)*B^3*S*T-pn*zn*Pn
  cn*(1-v)*T*dSupportDen v+2*dn*dZeroVertexNum v

noncomputable def dFNum (v x zn T : ℝ) : ℝ :=
  let rn := dFRadiusNum v x zn T
  240*dDeltaNum v*(60*dProbNum v x*dBetaNum v*(1-v)^2*(dBase v x)^3*T*dSupportDen v+rn)*
    (1-v)*(dBase v x)^3*dVacancyDen v x*T*dSupportDen v-11*rn^2

noncomputable def dFDen (v x T : ℝ) : ℝ :=
  5*(12*(1-v)^2*(dBase v x)^3*dVacancyDen v x*T*dSupportDen v)^2

noncomputable def dFFormula (lam x z : ℝ) : ℝ :=
  let rho := dhVacancyX lam x
  let P := dhParentUpperX .D lam x rho
  let c := eProbabilityX lam x*(2*P-alpha .D lam-beta .D lam)
  let d := gamma .D lam-delta .D lam-eProbabilityX lam x*z*P
  let b := eProbabilityX lam x*beta .D lam*rho
  let r := c+2*d*dSupportVertex lam 0
  4*delta .D lam*(b+r)-(11/5)*r^2

theorem dh_F_radius_clear (gn dn an bn pn Pn zn q B S T hn H : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q)+
      2*(gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2*S)))*(hn/H) =
      (pn*(2*Pn-(an+bn)*12*B^2*S)*q*T*H+
        2*((gn-dn)*12*q*B^3*S*T-pn*zn*Pn)*hn)/(12*q^2*B^3*S*T*H) := by
  field_simp
  <;> ring

theorem dh_F_clear (dn pn bn rn q B S T H : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q)*(pn/B*(bn/q)*(5*q*B/S)+rn/(12*q^2*B^3*S*T*H))-
      (11/5)*(rn/(12*q^2*B^3*S*T*H))^2 =
      (240*dn*(60*pn*bn*q^2*B^3*T*H+rn)*q*B^3*S*T*H-11*rn^2)/
        (5*(12*q^2*B^3*S*T*H)^2) := by
  field_simp
  <;> ring

theorem d_F_formula_coordinate (v x z zn T : ℝ)
    (hq : 1-v ≠ 0) (hB : dBase v x ≠ 0) (hS : dVacancyDen v x ≠ 0)
    (hT : T ≠ 0) (hH : dSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    dFFormula (dActivity v) x z = dFNum v x zn T/dFDen v x T := by
  unfold dFFormula
  dsimp only
  rw [d_parent_lower_coordinate v x hq hB hS, d_probability_coordinate v x hq hB,
    d_alpha_coordinate v hq, d_beta_coordinate v hq, d_gamma_coordinate v hq,
    d_delta_coordinate v hq, d_vacancy_coordinate v x hq hB hS,
    d_zero_vertex_coordinate v hq hH, hz]
  rw [dh_F_radius_clear _ _ _ _ _ _ _ _ _ _ _ _ _ hq hB hS hT hH]
  exact dh_F_clear _ _ _ _ _ _ _ _ _ hq hB hS hT hH

end F4Heavy.Analysis
