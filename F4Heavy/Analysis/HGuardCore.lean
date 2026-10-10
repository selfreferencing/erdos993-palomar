module

public import F4Heavy.Analysis.HPrimaryCoordinates
public import F4Heavy.Analysis.DUpperLogCoordinate

@[expose] public section
set_option autoImplicit false
namespace F4Heavy.Analysis
open F4Unified

theorem h_log_denominator_nonzero (x : ℝ) (hx : (1/4 : ℝ) ≤ x) :
    eLogDen x ≠ 0 := by
  have hx0 : 0 < x := by linarith only [hx]
  unfold eLogDen
  positivity

theorem h_C_clear (dn pn Pn an bn q B S : ℝ)
    (hq : q ≠ 0) (hB : B ≠ 0) (hS : S ≠ 0) :
    4*(dn/q)-(12/5)*(pn/B*(2*(Pn/(12*q*B^2*S))-an/q-bn/q)) =
      (240*dn*B^3*S-12*pn*(2*Pn-(an+bn)*12*B^2*S))/(60*q*B^3*S) := by
  field_simp
  <;> ring

end F4Heavy.Analysis
