module

public import F4Heavy.Analysis.DFormulaCoordinates
public import F4Heavy.Analysis.DHFactorSigns

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dAlphaNum (v : ℝ) : ℝ :=
  (46809*(1-v)+3327*((4/5)*(1+v)-(269/256)*(1-v)))/65536
noncomputable def dBetaNum (v : ℝ) : ℝ :=
  (35136*(1-v)+3086*((4/5)*(1+v)-(269/256)*(1-v)))/65536
noncomputable def dVacancyDen (v x : ℝ) : ℝ := (9-v)^2+20*(1-v^2)*x
noncomputable def dParentLowerNum (v x : ℝ) : ℝ :=
  dGammaNum v*dVacancyDen v x*(12*(dBase v x)^2-6*dProbNum v x*dBase v x-(dProbNum v x)^2)+
    60*(1-v)^2*(dBase v x)^2*(dBase v x-dProbNum v x)

theorem d_alpha_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    alpha .D (dActivity v) = dAlphaNum v/(1-v) := by
  norm_num [alpha, field, rowData, dActivity, dAlphaNum]
  field_simp
  <;> ring

theorem d_beta_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    beta .D (dActivity v) = dBetaNum v/(1-v) := by
  norm_num [beta, field, rowData, dActivity, dBetaNum]
  field_simp
  <;> ring

theorem d_coordinate_denominators (v x : ℝ)
    (hv : 0 ≤ v ∧ v ≤ (5/21 : ℝ)) (hx : (5/16 : ℝ) ≤ x ∧ x ≤ 1) :
    1-v ≠ 0 ∧ dBase v x ≠ 0 ∧ dVacancyDen v x ≠ 0 := by
  obtain ⟨_, hq, _, _, hB, hS, _⟩ := d_denominator_factor_signs v x hv hx
  refine ⟨ne_of_gt hq, ne_of_gt ?_, ne_of_gt ?_⟩
  · unfold dBase
    nlinarith only [hB]
  · unfold dVacancyDen
    nlinarith only [hS]

theorem d_vacancy_coordinate (v x : ℝ)
    (hq : 1-v ≠ 0) (hB : dBase v x ≠ 0) (hS : dVacancyDen v x ≠ 0) :
    dhVacancyX (dActivity v) x = 5*(1-v)*dBase v x/dVacancyDen v x := by
  unfold dhVacancyX
  rw [d_probability_coordinate v x hq hB]
  have he : 1+dActivity v*(1-dProbNum v x/dBase v x) =
      dVacancyDen v x/(5*(1-v)*dBase v x) := by
    unfold dActivity dVacancyDen
    field_simp
    unfold dBase dProbNum
    ring
  rw [he]
  field_simp

theorem dh_parent_lower_clear (gn pn q B S : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    gn/q*(1-pn/B/2-(pn/B)^2/12)+(1-pn/B)*(5*q*B/S) =
      (gn*S*(12*B^2-6*pn*B-pn^2)+60*q^2*B^2*(B-pn))/(12*q*B^2*S) := by
  field_simp
  <;> ring

theorem d_parent_lower_coordinate (v x : ℝ)
    (hq : 1-v ≠ 0) (hB : dBase v x ≠ 0) (hS : dVacancyDen v x ≠ 0) :
    dhParentUpperX .D (dActivity v) x (dhVacancyX (dActivity v) x) =
      dParentLowerNum v x/(12*(1-v)*(dBase v x)^2*dVacancyDen v x) := by
  unfold dhParentUpperX dhParentBaseX
  rw [d_probability_coordinate v x hq hB, d_gamma_coordinate v hq,
    d_vacancy_coordinate v x hq hB hS]
  exact dh_parent_lower_clear _ _ _ _ _ hq hB hS

theorem dh_C_clear (dn pn Pn an bn q B S : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    4*(dn/q)-(11/5)*(pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q)) =
      (240*dn*B^3*S-11*pn*(2*Pn-(an+bn)*12*B^2*S))/(60*q*B^3*S) := by
  field_simp
  <;> ring

end F4Heavy.Analysis
