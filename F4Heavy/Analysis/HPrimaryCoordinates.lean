module

public import F4Heavy.Analysis.HFormulaCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hVacancyDen (v x : ℝ) : ℝ := (11+3*v)^2+28*(1-v^2)*x
noncomputable def hParentUpperNum (v x : ℝ) : ℝ :=
  hGammaNum v*(12*(hBase v x)^2-6*hProbNum v x*hBase v x-(hProbNum v x)^2)+
    12*(1-v)*hBase v x*(hBase v x-hProbNum v x)
noncomputable def hParentLowerNum (v x : ℝ) : ℝ :=
  hGammaNum v*hVacancyDen v x*(12*(hBase v x)^2-6*hProbNum v x*hBase v x-(hProbNum v x)^2)+
    48*(1-v)^2*(hBase v x)^2*(hBase v x-hProbNum v x)
noncomputable def hNUpperNum (v x : ℝ) : ℝ :=
  3*(1-v)^2*(9+5*v)*x*hBase v x*(64-x^2)-2*(11+3*v)*hParentUpperNum v x
noncomputable def hNLowerNum (v x : ℝ) : ℝ :=
  3*(1-v)^2*(9+5*v)*x*hBase v x*(8-x)*(64*(1-v)*hBase v x-(8-x)*hVacancyDen v x)+
    24*hAlphaNum v*(11+3*v)*(hBase v x)^2*(hVacancyDen v x-4*(1-v)*hBase v x)-
    2*(11+3*v)*hParentLowerNum v x

theorem h_coordinate_denominators (v x : ℝ) (hv : 0 ≤ v ∧ v ≤ (1/7 : ℝ))
    (hx : (1/4 : ℝ) ≤ x ∧ x ≤ 1) :
    1-v ≠ 0 ∧ 11+3*v ≠ 0 ∧ hBase v x ≠ 0 ∧ hVacancyDen v x ≠ 0 := by
  have hv0 := hv.1
  have hx0 : 0 < x := by linarith only [hx.1]
  have hs : 0 < 1-v^2 := by nlinarith only [hv.1, hv.2, sq_nonneg (1-v)]
  refine ⟨ne_of_gt (by linarith only [hv.2]), ne_of_gt (by positivity), ?_, ?_⟩
  · unfold hBase
    positivity
  · unfold hVacancyDen
    positivity

theorem h_vacancy_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : hBase v x ≠ 0)
    (hS : hVacancyDen v x ≠ 0) :
    dhVacancyX (hActivity v) x = 4*(1-v)*hBase v x/hVacancyDen v x := by
  unfold dhVacancyX
  rw [h_probability_coordinate v x hq hB]
  have he : 1+hActivity v*(1-hProbNum v x/hBase v x) =
      hVacancyDen v x/(4*(1-v)*hBase v x) := by
    unfold hActivity
    field_simp [hq, hB]
    unfold hVacancyDen hProbNum hBase
    <;> ring
  rw [he]
  field_simp

theorem h_K_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 11+3*v ≠ 0) (hB : hBase v x ≠ 0) :
    eHeavyKX .H (hActivity v) x = 8*(1-v)*(9+5*v)*x/((11+3*v)*hBase v x) := by
  have ha : 1+hActivity v = (11+3*v)/(4*(1-v)) := by
    unfold hActivity
    field_simp
    <;> ring
  have hb : 1+hActivity v+hActivity v*x = hBase v x/(4*(1-v)) := by
    unfold hActivity hBase
    field_simp
    <;> ring
  unfold eHeavyKX
  rw [hb, ha]
  norm_num only [rowData]
  unfold hActivity
  field_simp
  <;> ring

theorem h_parent_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : hBase v x ≠ 0) :
    dhParentUpperX .H (hActivity v) x 1 = hParentUpperNum v x/(12*(1-v)*(hBase v x)^2) := by
  unfold dhParentUpperX dhParentBaseX
  rw [h_probability_coordinate v x hq hB, h_gamma_coordinate v hq]
  unfold hParentUpperNum
  field_simp
  <;> ring

theorem h_parent_lower_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : hBase v x ≠ 0)
    (hS : hVacancyDen v x ≠ 0) :
    dhParentUpperX .H (hActivity v) x (dhVacancyX (hActivity v) x) =
      hParentLowerNum v x/(12*(1-v)*(hBase v x)^2*hVacancyDen v x) := by
  unfold dhParentUpperX dhParentBaseX
  rw [h_probability_coordinate v x hq hB, h_gamma_coordinate v hq, h_vacancy_coordinate v x hq hB hS]
  unfold hParentLowerNum
  field_simp
  <;> ring

theorem h_N_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 11+3*v ≠ 0) (hB : hBase v x ≠ 0) :
    dhNFormula .H (hActivity v) x 1 = hNUpperNum v x/(24*(1-v)*(11+3*v)*(hBase v x)^2) := by
  unfold dhNFormula
  rw [h_K_coordinate v x hq hA hB, h_parent_upper_coordinate v x hq hB]
  norm_num only [dhTangentX, sub_self, mul_zero, add_zero]
  unfold hNUpperNum
  have hA' : 11+v*3 ≠ 0 := by simpa only [mul_comm] using hA
  field_simp [hA, hA']
  <;> ring

theorem h_N_lower_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hA : 11+3*v ≠ 0)
    (hB : hBase v x ≠ 0) (hS : hVacancyDen v x ≠ 0) :
    dhNFormula .H (hActivity v) x (dhVacancyX (hActivity v) x) =
      hNLowerNum v x/(24*(1-v)*(11+3*v)*(hBase v x)^2*hVacancyDen v x) := by
  unfold dhNFormula
  rw [h_K_coordinate v x hq hA hB, h_parent_lower_coordinate v x hq hB hS,
    h_vacancy_coordinate v x hq hB hS, h_alpha_coordinate v hq]
  norm_num only [dhTangentX]
  unfold hNLowerNum
  have hA' : 11+v*3 ≠ 0 := by simpa only [mul_comm] using hA
  field_simp [hA, hA']
  <;> ring

end F4Heavy.Analysis
