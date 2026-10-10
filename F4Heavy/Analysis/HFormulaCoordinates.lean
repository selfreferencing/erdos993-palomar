module

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHActivityCoordinates
public import F4Heavy.Analysis.EFormulaClearing

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def hActivity (v : ℝ) : ℝ := (7/4)*(1+v)/(1-v)
noncomputable def hBase (v x : ℝ) : ℝ := 11+3*v+7*(1+v)*x
noncomputable def hProbNum (v x : ℝ) : ℝ := 7*(1+v)*x
noncomputable def hAlphaNum (v : ℝ) : ℝ :=
  (51799*(1-v)+8158*((7/4)*(1+v)-(523/256)*(1-v)))/65536
noncomputable def hBetaNum (v : ℝ) : ℝ :=
  (20496*(1-v)+41265*((7/4)*(1+v)-(523/256)*(1-v)))/65536
noncomputable def hGammaNum (v : ℝ) : ℝ :=
  (29750*(1-v)+4333*((7/4)*(1+v)-(523/256)*(1-v)))/65536
noncomputable def hDeltaNum (v : ℝ) : ℝ :=
  (9083*(1-v)-11181*((7/4)*(1+v)-(523/256)*(1-v)))/65536
noncomputable def hLowerNum (v x : ℝ) : ℝ :=
  (1+x)*(activityLogLeft .H*(1-v)+(activityLogRight .H-activityLogLeft .H)*6*v)+
    2*(1-x)*(1-v)
noncomputable def hUpperNum (v x : ℝ) : ℝ :=
  eLogDen x*((1-v)*(activityLogMidpointUpper .H+1386294361120/1000000000000-21/73)+
    (42*(1+v)-49*(1-v))/73)-3*(9*x^2-1)*(1-v)

theorem h_probability_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : hBase v x ≠ 0) :
    eProbabilityX (hActivity v) x = hProbNum v x/hBase v x := by
  have hb : 1+hActivity v+hActivity v*x = hBase v x/(4*(1-v)) := by
    unfold hActivity hBase
    field_simp
    <;> ring
  unfold eProbabilityX
  rw [hb]
  unfold hActivity hProbNum
  field_simp
  <;> ring

theorem h_alpha_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    alpha .H (hActivity v) = hAlphaNum v/(1-v) := by
  norm_num [alpha, field, rowData, hActivity, hAlphaNum]
  field_simp
  <;> ring

theorem h_beta_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    beta .H (hActivity v) = hBetaNum v/(1-v) := by
  norm_num [beta, field, rowData, hActivity, hBetaNum]
  field_simp
  <;> ring

theorem h_gamma_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    gamma .H (hActivity v) = hGammaNum v/(1-v) := by
  norm_num [gamma, field, rowData, hActivity, hGammaNum]
  field_simp
  <;> ring

theorem h_delta_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    delta .H (hActivity v) = hDeltaNum v/(1-v) := by
  norm_num [delta, field, rowData, hActivity, hDeltaNum]
  field_simp
  <;> ring

theorem h_lower_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hC : 1+x ≠ 0) :
    parentLogLower .H (hActivity v) x = hLowerNum v x/((1-v)*(1+x)) := by
  norm_num [parentLogLower, activityLogLower, rowData, hActivity, hLowerNum]
  field_simp
  <;> ring

theorem h_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hT : eLogDen x ≠ 0) :
    parentLogUpper .H (hActivity v) x = hUpperNum v x/((1-v)*eLogDen x) := by
  rw [parentLogUpper_quotient .H (hActivity v) x hT]
  norm_num [eUpperNumerator, activityLogUpper, rowData, hActivity, hUpperNum]
  field_simp
  <;> ring

end F4Heavy.Analysis
