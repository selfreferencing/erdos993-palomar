module

public import F4Heavy.Analysis.HPrimaryCoordinates
public import F4Heavy.Analysis.HSupportCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hLowerWPiece (v x zn T : ℝ) (i : Fin 4) : ℝ :=
  let q := 1-v
  let A := 11+3*v
  let B := hBase v x
  let S := hVacancyDen v x
  let pn := hProbNum v x
  let Pn := hParentLowerNum v x
  let cn := pn*(2*Pn-(hAlphaNum v+hBetaNum v)*12*B^2*S)
  let dn := (hGammaNum v-hDeltaNum v)*12*q*B^3*S*T-pn*zn*Pn
  let H := hSupportDen v
  let hn := hVertexNum v 0
  match i with
  | 0 => 4*hDeltaNum v*pn*hNLowerNum v x*q^2*T^2*H^2
  | 1 => 384*hDeltaNum v*zn*pn*hBetaNum v*hn*q^2*A*B^3*T*H
  | 2 => 8*hDeltaNum v*zn*cn*hn*q*A*T*H
  | 3 => 8*hDeltaNum v*zn*dn*hn^2*A

noncomputable def hLowerWNum (v x zn T : ℝ) : ℝ :=
  hLowerWPiece v x zn T 0+hLowerWPiece v x zn T 1+
    hLowerWPiece v x zn T 2+hLowerWPiece v x zn T 3

noncomputable def hLowerWDen (v x T : ℝ) : ℝ :=
  24*(1-v)^4*(11+3*v)*(hBase v x)^3*hVacancyDen v x*T^2*(hSupportDen v)^2

theorem h_lower_W_clear (gn dn an bn pn Pn Nn zn hn q A B S T H : ℝ)
    (hq : q ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q)*(pn/B*(Nn/(24*q*A*B^2*S))+
      (zn/(q*T))*(pn/B)*(bn/q)*(4*q*B/S)*(hn/H))+
      4*(dn/q)*(zn/(q*T))*((pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q))*(hn/H)+
        (gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2*S)))*(hn/H)^2) =
      (4*dn*pn*Nn*q^2*T^2*H^2+384*dn*zn*pn*bn*hn*q^2*A*B^3*T*H+
        8*dn*zn*(pn*(2*Pn-(an+bn)*12*B^2*S))*hn*q*A*T*H+
        8*dn*zn*((gn-dn)*12*q*B^3*S*T-pn*zn*Pn)*hn^2*A)/
          (24*q^4*A*B^3*S*T^2*H^2) := by
  field_simp
  <;> ring

theorem h_lower_W_coordinate (v x z zn T : ℝ)
    (hq : 1-v ≠ 0) (hA : 11+3*v ≠ 0) (hB : hBase v x ≠ 0) (hS : hVacancyDen v x ≠ 0)
    (hT : T ≠ 0) (hH : hSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    dhWFormula .H (hActivity v) x (dhVacancyX (hActivity v) x) z
      (hSupportVertex (hActivity v) 0) 0 = hLowerWNum v x zn T/hLowerWDen v x T := by
  unfold dhWFormula
  dsimp only
  simp only [mul_zero, zero_mul, add_zero, sub_zero]
  rw [h_N_lower_coordinate v x hq hA hB hS, h_parent_lower_coordinate v x hq hB hS,
    h_probability_coordinate v x hq hB, h_alpha_coordinate v hq, h_beta_coordinate v hq,
    h_gamma_coordinate v hq, h_delta_coordinate v hq, h_vacancy_coordinate v x hq hB hS,
    h_lower_zero_vertex_coordinate v hq hH, hz]
  exact h_lower_W_clear _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hA hB hS hT hH

end F4Heavy.Analysis
