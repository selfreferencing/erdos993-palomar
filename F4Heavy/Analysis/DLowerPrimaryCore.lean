module

public import F4Heavy.Analysis.DPrimaryCoordinates
public import F4Heavy.Analysis.DZeroVertexCoordinate

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dLowerWPiece (v x zn T : ℝ) (i : Fin 4) : ℝ :=
  let q := 1-v
  let A := 9-v
  let B := dBase v x
  let S := dVacancyDen v x
  let pn := dProbNum v x
  let Pn := dParentLowerNum v x
  let cn := pn*(2*Pn-(dAlphaNum v+dBetaNum v)*12*B^2*S)
  let dn := (dGammaNum v-dDeltaNum v)*12*q*B^3*S*T-pn*zn*Pn
  let H := dSupportDen v
  let hn := dZeroVertexNum v
  match i with
  | 0 => 4*dDeltaNum v*pn*dNLowerNum v x*q^2*T^2*H^2
  | 1 => 24000*dDeltaNum v*zn*pn*dBetaNum v*hn*q^2*A*B^3*T*H
  | 2 => 400*dDeltaNum v*zn*cn*hn*q*A*T*H
  | 3 => 400*dDeltaNum v*zn*dn*hn^2*A

noncomputable def dLowerWNum (v x zn T : ℝ) : ℝ :=
  dLowerWPiece v x zn T 0+dLowerWPiece v x zn T 1+
    dLowerWPiece v x zn T 2+dLowerWPiece v x zn T 3

noncomputable def dLowerWDen (v x T : ℝ) : ℝ :=
  1200*(1-v)^4*(9-v)*(dBase v x)^3*dVacancyDen v x*T^2*(dSupportDen v)^2

theorem dh_lower_W_clear (gn dn an bn pn Pn Nn zn hn q A B S T H : ℝ)
    (hq : q ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q)*(pn/B*(Nn/(1200*q*A*B^2*S))+
      (zn/(q*T))*(pn/B)*(bn/q)*(5*q*B/S)*(hn/H))+
      4*(dn/q)*(zn/(q*T))*((pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q))*(hn/H)+
        (gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2*S)))*(hn/H)^2) =
      (4*dn*pn*Nn*q^2*T^2*H^2+24000*dn*zn*pn*bn*hn*q^2*A*B^3*T*H+
        400*dn*zn*(pn*(2*Pn-(an+bn)*12*B^2*S))*hn*q*A*T*H+
        400*dn*zn*((gn-dn)*12*q*B^3*S*T-pn*zn*Pn)*hn^2*A)/
          (1200*q^4*A*B^3*S*T^2*H^2) := by
  field_simp
  <;> ring

theorem d_lower_W_coordinate (v x z zn T : ℝ)
    (hq : 1-v ≠ 0) (hA : 9-v ≠ 0) (hB : dBase v x ≠ 0) (hS : dVacancyDen v x ≠ 0)
    (hT : T ≠ 0) (hH : dSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    dhWFormula .D (dActivity v) x (dhVacancyX (dActivity v) x) z
      (dSupportVertex (dActivity v) 0) 0 = dLowerWNum v x zn T/dLowerWDen v x T := by
  unfold dhWFormula
  dsimp only
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  rw [d_N_lower_coordinate v x hq hA hB hS, d_parent_lower_coordinate v x hq hB hS,
    d_probability_coordinate v x hq hB, d_alpha_coordinate v hq, d_beta_coordinate v hq,
    d_gamma_coordinate v hq, d_delta_coordinate v hq, d_vacancy_coordinate v x hq hB hS,
    d_zero_vertex_coordinate v hq hH, hz]
  exact dh_lower_W_clear _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hA hB hS hT hH

end F4Heavy.Analysis
