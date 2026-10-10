module

public import F4Heavy.Analysis.DPrimaryCoordinates
public import F4Heavy.Analysis.DSupportCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dUpperWPiece (v x zn T hn jn : ℝ) (i : Fin 5) : ℝ :=
  let q := 1-v
  let A := 9-v
  let B := dBase v x
  let pn := dProbNum v x
  let Pn := dParentUpperNum v x
  let cn := pn*(2*Pn-(dAlphaNum v+dBetaNum v)*12*B^2)
  let dn := (dGammaNum v-dDeltaNum v)*12*q*B^3*T-pn*zn*Pn
  let H := dSupportDen v
  let Gn := 12*dDeltaNum v*q*B^3*T*H+dn*jn
  match i with
  | 0 => 4*Gn*pn*dNUpperNum v x*q*T*H
  | 1 => 4800*Gn*zn*pn*dBetaNum v*hn*A*B^2
  | 2 => 4800*dDeltaNum v*zn*cn*hn*q*A*B^3*T*H
  | 3 => 4800*dDeltaNum v*zn*dn*hn^2*A*B^3
  | 4 => -100*zn*jn*cn^2*q*A*T*H

noncomputable def dUpperWNum (v x zn T hn jn : ℝ) : ℝ :=
  dUpperWPiece v x zn T hn jn 0+dUpperWPiece v x zn T hn jn 1+
    dUpperWPiece v x zn T hn jn 2+dUpperWPiece v x zn T hn jn 3+dUpperWPiece v x zn T hn jn 4

noncomputable def dUpperWDen (v x T : ℝ) : ℝ :=
  14400*(1-v)^4*(9-v)*(dBase v x)^6*T^2*(dSupportDen v)^2

theorem dh_upper_W_clear (gn dn an bn pn Pn Nn zn hn jn q A B T H : ℝ)
    (hq : q ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) (hT : T ≠ 0) (hH : H ≠ 0) :
    4*(dn/q+(gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2)))*(jn/H))*
      (pn/B*(Nn/(1200*q*A*B^2))+(zn/(q*T))*(pn/B)*(bn/q)*(hn/H))+
      4*(dn/q)*(zn/(q*T))*((pn/B*(2*(Pn/(12*q*B^2))-an/q-bn/q))*(hn/H)+
        (gn/q-dn/q-pn/B*(zn/(q*T))*(Pn/(12*q*B^2)))*(hn/H)^2)-
      (zn/(q*T))*(jn/H)*(pn/B*(2*(Pn/(12*q*B^2))-an/q-bn/q))^2 =
      (4*(12*dn*q*B^3*T*H+((gn-dn)*12*q*B^3*T-pn*zn*Pn)*jn)*pn*Nn*q*T*H+
        4800*(12*dn*q*B^3*T*H+((gn-dn)*12*q*B^3*T-pn*zn*Pn)*jn)*zn*pn*bn*hn*A*B^2+
        4800*dn*zn*(pn*(2*Pn-(an+bn)*12*B^2))*hn*q*A*B^3*T*H+
        4800*dn*zn*((gn-dn)*12*q*B^3*T-pn*zn*Pn)*hn^2*A*B^3+
        (-100*zn*jn*(pn*(2*Pn-(an+bn)*12*B^2))^2*q*A*T*H))/
          (14400*q^4*A*B^6*T^2*H^2) := by
  field_simp
  <;> ring

theorem d_upper_W_coordinate (v x z zn T : ℝ) (i : Fin 4)
    (hq : 1-v ≠ 0) (hA : 9-v ≠ 0) (hB : dBase v x ≠ 0)
    (hT : T ≠ 0) (hH : dSupportDen v ≠ 0) (hz : z = zn/((1-v)*T)) :
    dhWFormula .D (dActivity v) x 1 z (dSupportVertex (dActivity v) i) (dSupportHeight (dActivity v) i) =
      dUpperWNum v x zn T (dVertexNum v i) (dHeightNum v i)/dUpperWDen v x T := by
  unfold dhWFormula
  dsimp only
  rw [d_N_upper_coordinate v x hq hA hB, d_parent_upper_coordinate v x hq hB,
    d_probability_coordinate v x hq hB, d_alpha_coordinate v hq, d_beta_coordinate v hq,
    d_gamma_coordinate v hq, d_delta_coordinate v hq, d_vertex_coordinate v i hq hH,
    d_height_coordinate v i hq hH, hz]
  simp only [mul_one]
  exact dh_upper_W_clear _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq hA hB hT hH

end F4Heavy.Analysis
