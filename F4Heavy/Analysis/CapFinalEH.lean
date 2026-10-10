module

public import F4Heavy.Analysis.CapReserveMonotone
public import F4Heavy.Analysis.CapResponseSigns

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_nonD_activity_lower (r : Row) (lam : ℝ) (hr : InRow r lam) (hn : r ≠ .D) :
    13 / 10 ≤ lam := by
  cases r with
  | D => exact (hn rfl).elim
  | E1 => exact hr.1
  | E2 => norm_num [InRow, rowData] at hr; linarith only [hr.1]
  | H => norm_num [InRow, rowData] at hr; linarith only [hr.1]

theorem cap_reserve_increment_nonD (r : Row) (lam Y rho u : ℝ) (hr : InRow r lam)
    (hn : r ≠ .D) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hu : 0 < u) (huc : u ≤ capChild lam Y) :
    (childH u - childH (capChild lam Y)) / 500 ≤
      capB r lam Y rho * (childH u - childH (capChild lam Y)) + delta r lam *
        ((childH u) ^ 2 / childJ lam u -
          (childH (capChild lam Y)) ^ 2 / childJ lam (capChild lam Y)) := by
  have hl := inRow_activity_pos r lam hr
  have hh := cap_height_increment_on_domain lam Y u hl hu.le huc
  have hd : 0 ≤ childH u - childH (capChild lam Y) := by linarith only [hh, huc]
  have hb := mul_le_mul_of_nonneg_right (cap_b_uniform_lower r lam Y rho hr hH hrho) hd
  have hw := cap_reserve_quotient_antitone lam u (capChild lam Y)
    (cap_nonD_activity_lower r lam hr hn) hu huc (min_le_right _ _)
  have hg := mul_nonneg (row_delta_pos r lam hr).le (sub_nonneg.mpr hw)
  linarith only [hb, hg]

theorem cap_scalar_bounds_nonD (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hn : r ≠ .D) (hY : 0 < Y) (hH : parentH Y ≤ q lam)
    (hrho : FeasibleVacancy lam Y rho) : CapScalarBounds r lam Y rho := by
  apply cap_scalar_bounds_from_reserve_increment r lam Y rho hr hY hH hrho
  intro u hu huc
  exact cap_reserve_increment_nonD r lam Y rho u hr hn hH hrho hu huc

theorem fixedParentCap_nonD (r : Row) (hn : r ≠ .D) : FixedParentCap r := by
  apply fixedParentCap_of_scalar_bounds
  intro lam Y rho hr hY hH hrho
  exact cap_scalar_bounds_nonD r lam Y rho hr hn hY hH hrho

end F4Heavy.Analysis
