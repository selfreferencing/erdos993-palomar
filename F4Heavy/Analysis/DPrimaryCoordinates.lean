module

public import F4Heavy.Analysis.DLowerCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dParentUpperNum (v x : ℝ) : ℝ :=
  dGammaNum v*(12*(dBase v x)^2-6*dProbNum v x*dBase v x-(dProbNum v x)^2)+
    12*(1-v)*dBase v x*(dBase v x-dProbNum v x)

noncomputable def dNUpperNum (v x : ℝ) : ℝ :=
  4653*(1-v)^2*(13+3*v)*x*dBase v x-100*(9-v)*dParentUpperNum v x

noncomputable def dNLowerNum (v x : ℝ) : ℝ :=
  3*(1-v)^2*dBase v x*(13+3*v)*x*(13200*(1-v)*dBase v x-1089*dVacancyDen v x)+
    1200*dAlphaNum v*(9-v)*(dBase v x)^2*(dVacancyDen v x-5*(1-v)*dBase v x)-
    100*(9-v)*dParentLowerNum v x

theorem d_K_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 9-v ≠ 0) (hB : dBase v x ≠ 0) :
    eHeavyKX .D (dActivity v) x = 4*(1-v)*(13+3*v)*x/((9-v)*dBase v x) := by
  have ha : 1+dActivity v = (9-v)/(5*(1-v)) := by
    unfold dActivity
    field_simp
    <;> ring
  have hb : 1+dActivity v+dActivity v*x = dBase v x/(5*(1-v)) := by
    unfold dActivity dBase
    field_simp
    <;> ring
  unfold eHeavyKX
  rw [hb, ha]
  norm_num only [rowData]
  unfold dActivity
  field_simp
  <;> ring

theorem d_parent_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : dBase v x ≠ 0) :
    dhParentUpperX .D (dActivity v) x 1 = dParentUpperNum v x/(12*(1-v)*(dBase v x)^2) := by
  unfold dhParentUpperX dhParentBaseX
  rw [d_probability_coordinate v x hq hB, d_gamma_coordinate v hq]
  unfold dParentUpperNum
  field_simp
  <;> ring

theorem d_N_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 9-v ≠ 0) (hB : dBase v x ≠ 0) :
    dhNFormula .D (dActivity v) x 1 = dNUpperNum v x/(1200*(1-v)*(9-v)*(dBase v x)^2) := by
  unfold dhNFormula
  rw [d_K_coordinate v x hq hA hB, d_parent_upper_coordinate v x hq hB]
  norm_num only [dhTangentX, sub_self, mul_zero, add_zero]
  unfold dNUpperNum
  field_simp
  <;> ring

theorem d_N_lower_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 9-v ≠ 0)
    (hB : dBase v x ≠ 0) (hS : dVacancyDen v x ≠ 0) :
    dhNFormula .D (dActivity v) x (dhVacancyX (dActivity v) x) =
      dNLowerNum v x/(1200*(1-v)*(9-v)*(dBase v x)^2*dVacancyDen v x) := by
  unfold dhNFormula
  rw [d_K_coordinate v x hq hA hB, d_parent_lower_coordinate v x hq hB hS,
    d_vacancy_coordinate v x hq hB hS, d_alpha_coordinate v hq]
  norm_num only [dhTangentX]
  unfold dNLowerNum
  field_simp
  <;> ring

end F4Heavy.Analysis
