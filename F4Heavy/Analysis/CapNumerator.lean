module

public import F4Heavy.Analysis.CapGuard11D
public import F4Heavy.Analysis.CapGuard11E1
public import F4Heavy.Analysis.CapGuard11E2
public import F4Heavy.Analysis.CapGuard11H

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_reserve_scalar_guard (r : Row) (lam : ℝ) (hr : InRow r lam) :
    capCUpper r lam * (2 * lam / (6 + lam)) < 2 * delta r lam := by
  cases r with
  | D => exact cap_guard11_D_positive lam hr
  | E1 => exact cap_guard11_E1_positive lam hr
  | E2 => exact cap_guard11_E2_positive lam hr
  | H => exact cap_guard11_H_positive lam hr

theorem cap_response_numerator_positive (r : Row) (lam Y rho u : ℝ)
    (hr : InRow r lam) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) :
    0 < 2 * delta r lam * childH u - capC r lam Y rho * childJ lam u := by
  exact cap_response_numerator_positive_of_guard r lam Y rho u hr hH hrho hu huc
    (cap_reserve_scalar_guard r lam hr)

end F4Heavy.Analysis
