module

public import F4Heavy.Analysis.CapResponseBounds
public import F4Heavy.Analysis.CapReserveUpper

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified
noncomputable section

def capCUpper (r : Row) (lam : ℝ) : ℝ :=
  if r = .H then (2 + 2 * gamma r lam - alpha r lam - beta r lam) ^ 2 /
      (4 * (2 + gamma r lam))
  else (lam / (1 + 2 * lam)) * ((2 + 2 * gamma r lam - alpha r lam - beta r lam) -
      (2 + gamma r lam) * (lam / (1 + 2 * lam)))

theorem cap_parabola_orientation_D (lam : ℝ) (hr : InRow .D lam) :
    0 ≤ (1 + 2 * lam) * (alpha .D lam + beta .D lam) -
      2 * (1 + lam) * gamma .D lam - 2 := by
  have hr' := hr
  norm_num [InRow, rowData] at hr'
  have hA : 6 / 5 < alpha .D lam + beta .D lam := by
    norm_num [alpha, beta, field, rowData]
    linarith only [hr'.1]
  have hg : gamma .D lam < 7 / 25 := by
    norm_num [gamma, field, rowData]
    linarith only [hr'.2]
  have h1 := mul_lt_mul_of_pos_left hA (show 0 < 1 + 2 * lam by linarith only [hr'.1])
  have h2 := mul_lt_mul_of_pos_left hg (show 0 < 2 * (1 + lam) by linarith only [hr'.1])
  linarith only [h1, h2, hr'.1]

theorem cap_parabola_orientation_E (r : Row) (lam : ℝ) (he : r = .E1 ∨ r = .E2)
    (hr : InRow r lam) :
    0 ≤ (1 + 2 * lam) * (alpha r lam + beta r lam) -
      2 * (1 + lam) * gamma r lam - 2 := by
  have hrange : 13 / 10 ≤ lam := by
    rcases he with rfl | rfl <;> norm_num [InRow, rowData] at hr <;> linarith only [hr.1]
  have hA : 1 < alpha r lam + beta r lam := by
    rcases he with rfl | rfl <;> norm_num [InRow, rowData] at hr <;>
      norm_num [alpha, beta, field, rowData] <;> linarith only [hr.1]
  have hg : gamma r lam < 1 / 3 := by
    rcases he with rfl | rfl <;> norm_num [InRow, rowData] at hr <;>
      norm_num [gamma, field, rowData] <;> linarith only [hr.2]
  have h1 := mul_lt_mul_of_pos_left hA (show 0 < 1 + 2 * lam by linarith only [hrange])
  have h2 := mul_lt_mul_of_pos_left hg (show 0 < 2 * (1 + lam) by linarith only [hrange])
  linarith only [h1, h2, hrange]

theorem cap_parabola_endpoint_orientation (r : Row) (lam : ℝ) (hr : InRow r lam)
    (hnot : r ≠ .H) :
    2 + 2 * gamma r lam - alpha r lam - beta r lam ≤
      2 * (2 + gamma r lam) * (lam / (1 + 2 * lam)) := by
  have hl := inRow_activity_pos r lam hr
  have hg : 0 ≤ (1 + 2 * lam) * (alpha r lam + beta r lam) -
      2 * (1 + lam) * gamma r lam - 2 := by
    cases r with
    | D => exact cap_parabola_orientation_D lam hr
    | E1 => exact cap_parabola_orientation_E .E1 lam (Or.inl rfl) hr
    | E2 => exact cap_parabola_orientation_E .E2 lam (Or.inr rfl) hr
    | H => exact (hnot rfl).elim
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (show 0 < 1 + 2 * lam by linarith)).mpr
  nlinarith only [hg]

theorem cap_c_uniform_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho) :
    capC r lam Y rho ≤ capCUpper r lam := by
  unfold capCUpper
  by_cases he : r = .H
  · rw [if_pos he]
    exact cap_c_vertex_upper r lam Y rho hr hrho
  · rw [if_neg he]
    exact cap_c_endpoint_upper r lam Y rho hr hH hrho
      (cap_parabola_endpoint_orientation r lam hr he)

theorem cap_response_numerator_positive_of_guard (r : Row) (lam Y rho u : ℝ)
    (hr : InRow r lam) (hH : parentH Y ≤ q lam) (hrho : FeasibleVacancy lam Y rho)
    (hu : 0 < u) (huc : u ≤ capChild lam Y)
    (hguard : capCUpper r lam * (2 * lam / (6 + lam)) < 2 * delta r lam) :
    0 < 2 * delta r lam * childH u - capC r lam Y rho * childJ lam u := by
  have hl := inRow_activity_pos r lam hr
  exact cap_response_numerator_of_reserve_bound _ _ _ _ _ _
    (cap_child_height_bounds lam Y u hl hu huc).1
    (cap_child_reserve_pos lam Y u hl hu huc).le (row_delta_pos r lam hr)
    (cap_c_uniform_upper r lam Y rho hr hH hrho)
    (cap_childJ_reserve_upper r lam Y u hr hu huc) hguard

end
end F4Heavy.Analysis
