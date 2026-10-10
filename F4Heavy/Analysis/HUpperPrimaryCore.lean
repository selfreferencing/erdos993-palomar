module

public import F4Heavy.Analysis.HPrimaryCoordinates
public import F4Heavy.Analysis.HSupportCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hUpperWPiece (v x zn T hn jn : ℝ) (i : Fin 5) : ℝ :=
  let q := 1-v
  let A := 11+3*v
  let B := hBase v x
  let pn := hProbNum v x
  let Pn := hParentUpperNum v x
  let cn := pn*(2*Pn-(hAlphaNum v+hBetaNum v)*12*B^2)
  let dn := (hGammaNum v-hDeltaNum v)*12*q*B^3*T-pn*zn*Pn
  let H := hSupportDen v
  let Gn := 12*hDeltaNum v*q*B^3*T*H+dn*jn
  match i with
  | 0 => 4*Gn*pn*hNUpperNum v x*q*T*H
  | 1 => 96*Gn*zn*pn*hBetaNum v*hn*A*B^2
  | 2 => 96*hDeltaNum v*zn*cn*hn*q*A*B^3*T*H
  | 3 => 96*hDeltaNum v*zn*dn*hn^2*A*B^3
  | 4 => -2*zn*jn*cn^2*q*A*T*H

noncomputable def hUpperWNum (v x zn T hn jn : ℝ) : ℝ :=
  hUpperWPiece v x zn T hn jn 0+hUpperWPiece v x zn T hn jn 1+
    hUpperWPiece v x zn T hn jn 2+hUpperWPiece v x zn T hn jn 3+hUpperWPiece v x zn T hn jn 4

noncomputable def hUpperWDen (v x T : ℝ) : ℝ :=
  288*(1-v)^4*(11+3*v)*(hBase v x)^6*T^2*(hSupportDen v)^2

theorem h_upper_W_clear (gn dn an bn pn Pn Nn zn hn jn q A B T H : ℝ)
    (hq : q ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q+(gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2)))*(jn/H))*
      (pn/B*(Nn/(24*q*A*B^2))+(zn/(q*T))*(pn/B)*(bn/q)*(hn/H))+
      4*(dn/q)*(zn/(q*T))*((pn/B*(2*(Pn/(12*q*B^2))-an/q-bn/q))*(hn/H)+
        (gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2)))*(hn/H)^2)-
      (zn/(q*T))*(jn/H)*(pn/B*(2*(Pn/(12*q*B^2))-an/q-bn/q))^2 =
      (4*(12*dn*q*B^3*T*H+((gn-dn)*12*q*B^3*T-pn*zn*Pn)*jn)*pn*Nn*q*T*H+
        96*(12*dn*q*B^3*T*H+((gn-dn)*12*q*B^3*T-pn*zn*Pn)*jn)*zn*pn*bn*hn*A*B^2+
        96*dn*zn*(pn*(2*Pn-(an+bn)*12*B^2))*hn*q*A*B^3*T*H+
        96*dn*zn*((gn-dn)*12*q*B^3*T-pn*zn*Pn)*hn^2*A*B^3+
        (-2*zn*jn*(pn*(2*Pn-(an+bn)*12*B^2))^2*q*A*T*H))/
          (288*q^4*A*B^6*T^2*H^2) := by
  field_simp
  <;> ring

theorem h_upper_W_coordinate (v x z zn T : ℝ) (i : Fin 5)
    (hq : 1-v ≠ 0) (hA : 11+3*v ≠ 0) (hB : hBase v x ≠ 0)
    (hT : T ≠ 0) (hH : hSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    dhWFormula .H (hActivity v) x 1 z (hUpperSupportVertex (hActivity v) i) (hUpperSupportHeight (hActivity v) i) =
      hUpperWNum v x zn T (hVertexNum v i) (hHeightNum v i)/hUpperWDen v x T := by
  unfold dhWFormula
  dsimp only
  rw [h_N_upper_coordinate v x hq hA hB, h_parent_upper_coordinate v x hq hB,
    h_probability_coordinate v x hq hB, h_alpha_coordinate v hq, h_beta_coordinate v hq,
    h_gamma_coordinate v hq, h_delta_coordinate v hq, h_upper_vertex_coordinate v i hq hH,
    h_upper_height_coordinate v i hq hH, hz]
  simp only [mul_one]
  exact h_upper_W_clear _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hA hB hT hH

end F4Heavy.Analysis
