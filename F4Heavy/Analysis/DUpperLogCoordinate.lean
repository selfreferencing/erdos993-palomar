module

public import F4Heavy.Analysis.DLowerCoordinates
public import F4Heavy.Analysis.EFormulaClearing

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

noncomputable def dUpperNum (v x : ℝ) : ℝ :=
  eLogDen x*((1-v)*(activityLogMidpointUpper .D+1386294361120/1000000000000-21/73)+
    (16*(1+v)-21*(1-v))/41)-3*(9*x^2-1)*(1-v)

theorem d_upper_coordinate (v x : ℝ) (hq : 1-v ≠ 0) (hT : eLogDen x ≠ 0) :
    parentLogUpper .D (dActivity v) x = dUpperNum v x/((1-v)*eLogDen x) := by
  rw [parentLogUpper_quotient .D (dActivity v) x hT]
  norm_num [eUpperNumerator, activityLogUpper, rowData, dActivity, dUpperNum]
  field_simp
  <;> ring

theorem d_log_denominator_nonzero (x : ℝ) (hx : (5/16 : ℝ) ≤ x) :
    eLogDen x ≠ 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  unfold eLogDen
  positivity

theorem dh_R_clear (gn dn pn Pn an bn un q B S T : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) (hT : T ≠ 0) :
    pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q)+
      2*(gn/q-dn/q-pn/B*(un/(q*T))*(Pn/(12*q*B^2*S))) =
      (pn*(2*Pn-(an+bn)*12*B^2*S)*q*T+24*(gn-dn)*q*B^3*S*T-
        2*pn*un*Pn)/(12*q^2*B^3*S*T) := by
  field_simp
  <;> ring

end F4Heavy.Analysis
