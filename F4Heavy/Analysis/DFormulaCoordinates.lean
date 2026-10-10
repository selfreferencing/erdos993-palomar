module

public import F4Heavy.Analysis.DHFormulaCore
public import F4Heavy.Analysis.DHActivityCoordinates

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dActivity (v : ℝ) : ℝ := (4/5)*(1+v)/(1-v)
noncomputable def dBase (v x : ℝ) : ℝ := 9-v+4*(1+v)*x
noncomputable def dProbNum (v x : ℝ) : ℝ := 4*(1+v)*x
noncomputable def dGammaNum (v : ℝ) : ℝ :=
  (14520*(1-v)+13694*((4/5)*(1+v)-(269/256)*(1-v)))/65536
noncomputable def dDeltaNum (v : ℝ) : ℝ :=
  (1835*(1-v)+1340*((4/5)*(1+v)-(269/256)*(1-v)))/65536
noncomputable def dLowerNum (v x : ℝ) : ℝ :=
  (1+x)*(activityLogLeft .D*(1-v)+(activityLogRight .D-activityLogLeft .D)*(16/5)*v)+
    2*(1-x)*(1-v)

theorem d_probability_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hB : dBase v x ≠ 0) :
    eProbabilityX (dActivity v) x = dProbNum v x/dBase v x := by
  have hb : 1+dActivity v+dActivity v*x = dBase v x/(5*(1-v)) := by
    unfold dActivity dBase
    field_simp
    <;> ring
  unfold eProbabilityX
  rw [hb]
  unfold dActivity dProbNum
  field_simp
  <;> ring

theorem d_gamma_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    gamma .D (dActivity v) = dGammaNum v/(1-v) := by
  norm_num [gamma, field, rowData, dActivity, dGammaNum]
  field_simp
  <;> ring

theorem d_delta_coordinate (v : ℝ) (hq : 1-v ≠ 0) :
    delta .D (dActivity v) = dDeltaNum v/(1-v) := by
  norm_num [delta, field, rowData, dActivity, dDeltaNum]
  field_simp
  <;> ring

theorem d_lower_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hC : 1+x ≠ 0) :
    parentLogLower .D (dActivity v) x = dLowerNum v x/((1-v)*(1+x)) := by
  norm_num [parentLogLower, activityLogLower, rowData, dActivity, dLowerNum]
  field_simp
  <;> ring

theorem dh_curvature_clear (pn ln gn dn q B C : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    pn/B*(ln/(q*C))*(gn/q*(1-pn/B/2-(pn/B)^2/12)+(1-pn/B))-(gn/q-dn/q) =
      (pn*ln*(gn*(12*B^2-6*pn*B-pn^2)+12*q*B*(B-pn))-
        (gn-dn)*12*q*B^3*C)/(12*q^2*B^3*C) := by
  field_simp
  <;> ring

end F4Heavy.Analysis
