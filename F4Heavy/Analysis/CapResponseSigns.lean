module

public import F4Heavy.Analysis.CapSlopeAssembly
public import F4Heavy.Analysis.CapSlopeGuardD4
public import F4Heavy.Analysis.CapSlopeGuardD5
public import F4Heavy.Analysis.CapSlopeGuardE14
public import F4Heavy.Analysis.CapSlopeGuardE15
public import F4Heavy.Analysis.CapSlopeGuardE24
public import F4Heavy.Analysis.CapSlopeGuardE25
public import F4Heavy.Analysis.CapSlopeGuardH4
public import F4Heavy.Analysis.CapSlopeGuardH5
public import F4Heavy.Analysis.CapSlopeGuardH6
public import F4Heavy.Analysis.CapSlopeGuardH7

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_lambda_lower_endpoint_positive (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < capLambda r lam (2 * (lam + 2) / (3 * lam + 4)) := by
  cases r with
  | D => linarith only [cap_slope_D_4_positive lam hr]
  | E1 => linarith only [cap_slope_E1_4_positive lam hr]
  | E2 => linarith only [cap_slope_E2_4_positive lam hr]
  | H => linarith only [cap_slope_H_4_positive lam hr]

theorem cap_lambda_upper_endpoint_positive (r : Row) (lam : ℝ) (hr : InRow r lam) :
    0 < capLambda r lam 1 := by
  cases r with
  | D => linarith only [cap_slope_D_5_positive lam hr]
  | E1 => linarith only [cap_slope_E1_5_positive lam hr]
  | E2 => linarith only [cap_slope_E2_5_positive lam hr]
  | H => linarith only [cap_slope_H_5_positive lam hr]

theorem cap_response_signs (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hY : 0 ≤ Y) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    0 < capC r lam Y rho + 2 * capD r lam Y rho ∧
      ∀ u, 0 < u → u ≤ capChild lam Y →
        0 < capC r lam Y rho + 2 * capD r lam Y rho * childH u := by
  apply cap_response_signs_from_scalar_bounds r lam Y rho hr hY hH hrho
    (cap_lambda_lower_endpoint_positive r lam hr)
    (cap_lambda_upper_endpoint_positive r lam hr)
  · intro he
    subst r
    linarith only [cap_slope_H_7_positive lam hr]
  · intro he
    subst r
    linarith only [cap_slope_H_6_positive lam hr]

theorem cap_scalar_bounds_from_reserve_increment (r : Row) (lam Y rho : ℝ)
    (hr : InRow r lam) (hY : 0 < Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho)
    (hincrement : ∀ u, 0 < u → u ≤ capChild lam Y →
      (childH u - childH (capChild lam Y)) / 500 ≤
        capB r lam Y rho * (childH u - childH (capChild lam Y)) + delta r lam *
        ((childH u) ^ 2 / childJ lam u -
          (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y))) :
    CapScalarBounds r lam Y rho :=
  cap_scalar_bounds_from_slope_and_increment r lam Y rho hr hY hH hrho
    (cap_response_signs r lam Y rho hr hY.le hH hrho) hincrement

end F4Heavy.Analysis
