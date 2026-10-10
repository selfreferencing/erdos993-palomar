module

public import F4Heavy.Analysis.HeavyReduction
public import F4Heavy.Analysis.LogBounds

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem row_gamma_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < gamma r lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;>
    simp only [gamma, field, rowData] <;> nlinarith [hr.1, hr.2]

theorem parentP_linear_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam) :
    parentP r lam Y rho ≤ rho * (1 - p lam Y) + gamma r lam * (1 - p lam Y / 2) := by
  have hlam := inRow_activity_pos r lam hr
  have hb := probability_log_ratio_linear_upper (p lam Y) (p_pos lam Y hlam) (p_lt_one lam Y hlam)
  have hm := mul_le_mul_of_nonneg_left hb (row_gamma_pos r lam hr).le
  unfold parentP
  rw [mul_div_assoc]
  exact add_le_add le_rfl hm

theorem parentP_quadratic_upper (r : Row) (lam Y rho : ℝ) (hr : InRow r lam) :
    parentP r lam Y rho ≤ rho * (1 - p lam Y) +
      gamma r lam * (1 - p lam Y / 2 - (p lam Y) ^ 2 / 12) := by
  have hlam := inRow_activity_pos r lam hr
  have hb := probability_log_ratio_quadratic_upper (p lam Y) (p_pos lam Y hlam) (p_lt_one lam Y hlam)
  have hm := mul_le_mul_of_nonneg_left hb (row_gamma_pos r lam hr).le
  unfold parentP
  rw [mul_div_assoc]
  exact add_le_add le_rfl hm

theorem parentP_positive (r : Row) (lam Y rho : ℝ) (hr : InRow r lam)
    (hrho : FeasibleVacancy lam Y rho) : 0 < parentP r lam Y rho := by
  have hlam := inRow_activity_pos r lam hr
  have hp := p_pos lam Y hlam
  have hp1 := p_lt_one lam Y hlam
  have hrhop := feasible_vacancy_pos lam Y rho hlam hrho
  have hg := row_gamma_pos r lam hr
  have hl := Real.log_neg (show 0 < 1 - p lam Y by linarith) (show 1 - p lam Y < 1 by linarith)
  unfold parentP
  exact add_pos (mul_pos hrhop (by linarith)) (div_pos (mul_pos hg hp) (by linarith))

end F4Heavy.Analysis
