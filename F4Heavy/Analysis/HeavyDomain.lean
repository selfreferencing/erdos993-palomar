module

public import F4Heavy.Analysis.PaymentReduction

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem inRow_activity_pos (r : Row) (lam : ℝ) (hr : InRow r lam) : 0 < lam := by
  cases r <;> norm_num [InRow, rowData] at hr <;> linarith [hr.1]

theorem q_pos (lam : ℝ) (hlam : 0 < lam) : 0 < q lam := by
  exact div_pos hlam (by linarith)

theorem q_lt_one (lam : ℝ) (hlam : 0 < lam) : q lam < 1 := by
  unfold q
  exact (div_lt_one (by linarith : 0 < 1 + lam)).2 (by linarith)

theorem p_pos (lam Y : ℝ) (hlam : 0 < lam) : 0 < p lam Y := by
  unfold p
  exact div_pos (mul_pos hlam (Real.exp_pos _)) (by positivity)

theorem p_lt_one (lam Y : ℝ) (hlam : 0 < lam) : p lam Y < 1 := by
  unfold p
  apply (div_lt_one (by positivity : 0 < 1 + lam * Real.exp (-Y))).2
  linarith

theorem p_le_q (lam Y : ℝ) (hlam : 0 < lam) (hY : 0 ≤ Y) : p lam Y ≤ q lam := by
  have he : Real.exp (-Y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold p q
  apply (div_le_div_iff₀ (by positivity : 0 < 1 + lam * Real.exp (-Y))
    (by linarith : 0 < 1 + lam)).2
  nlinarith

theorem feasible_vacancy_pos (lam Y rho : ℝ) (hlam : 0 < lam)
    (hrho : FeasibleVacancy lam Y rho) : 0 < rho := by
  have hp := p_lt_one lam Y hlam
  have hd : 0 < 1 + lam * (1 - p lam Y) := by positivity
  exact lt_of_lt_of_le (one_div_pos.mpr hd) hrho.1

theorem heavy_child_cap (lam Y : ℝ) (hlam : 0 < lam) (hx : parentX lam Y ≤ 1) :
    childCap lam Y = q lam := by
  unfold childCap
  apply min_eq_left
  unfold q parentH
  apply (div_le_iff₀ (by linarith : 0 < 1 + lam)).2
  unfold parentX at hx
  nlinarith

theorem f_first_branch (lam t : ℝ) (hlam : 0 < lam) (ht : (1 + q lam) * t ≤ q lam) :
    f lam t = (1 + q lam) / (2 * q lam) * t := by
  have hq := q_pos lam hlam
  have hq1 := q_lt_one lam hlam
  unfold f
  apply max_eq_left
  have hid : (1 + q lam) / (2 * (q lam) ^ 2) * t +
      (q lam - 1) / (2 * q lam) - (1 + q lam) / (2 * q lam) * t =
      (1 - q lam) * ((1 + q lam) * t - q lam) / (2 * (q lam) ^ 2) := by
    field_simp
    <;> ring
  have hnum : (1 - q lam) * ((1 + q lam) * t - q lam) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by nlinarith) (by linarith)
  have hdiv := div_nonpos_of_nonpos_of_nonneg hnum
    (by positivity : 0 ≤ 2 * (q lam) ^ 2)
  linarith

theorem f_second_branch (lam t : ℝ) (hlam : 0 < lam) (ht : q lam ≤ (1 + q lam) * t) :
    f lam t = (1 + q lam) / (2 * (q lam) ^ 2) * t +
      (q lam - 1) / (2 * q lam) := by
  have hq := q_pos lam hlam
  have hq1 := q_lt_one lam hlam
  unfold f
  apply max_eq_right
  have hid : (1 + q lam) / (2 * (q lam) ^ 2) * t +
      (q lam - 1) / (2 * q lam) - (1 + q lam) / (2 * q lam) * t =
      (1 - q lam) * ((1 + q lam) * t - q lam) / (2 * (q lam) ^ 2) := by
    field_simp
    <;> ring
  have hnum : 0 ≤ (1 - q lam) * ((1 + q lam) * t - q lam) :=
    mul_nonneg (by linarith) (by linarith)
  have hdiv := div_nonneg hnum (by positivity : 0 ≤ 2 * (q lam) ^ 2)
  linarith

theorem heavy_parent_probability_bound (lam Y : ℝ) (hlam : 0 < lam)
    (hx : parentX lam Y ≤ 1) : (1 + q lam) * p lam Y ≤ q lam := by
  have he := Real.exp_pos (-Y)
  have hd1 : 0 < 1 + lam := by linarith
  have hd2 : 0 < 1 + lam * Real.exp (-Y) := by positivity
  unfold parentX at hx
  unfold q p
  apply (le_div_iff₀ hd1).2
  have hid : (1 + lam / (1 + lam)) * (lam * Real.exp (-Y) /
      (1 + lam * Real.exp (-Y))) * (1 + lam) =
      ((1 + 2 * lam) * lam * Real.exp (-Y)) / (1 + lam * Real.exp (-Y)) := by
    field_simp
    <;> ring
  rw [hid]
  apply (div_le_iff₀ hd2).2
  nlinarith [mul_nonneg hlam.le (sub_nonneg.mpr hx)]

theorem feasible_source_max (lam Y rho : ℝ) (hlam : 0 < lam)
    (hrho : FeasibleVacancy lam Y rho) :
    max (1 - rho) ((1 - p lam Y * rho) * q lam) =
      (1 - p lam Y * rho) * q lam := by
  have hp := p_lt_one lam Y hlam
  have hden : 0 < 1 + lam * (1 - p lam Y) := by positivity
  have hmul : 1 ≤ rho * (1 + lam * (1 - p lam Y)) :=
    (div_le_iff₀ hden).mp hrho.1
  apply max_eq_right
  unfold q
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by linarith : 0 < 1 + lam)).2
  nlinarith

theorem heavy_source_identity (lam Y rho : ℝ) (hlam : 0 < lam)
    (hrho : FeasibleVacancy lam Y rho) (hx : parentX lam Y ≤ 1) :
    source lam Y rho = (1 + q lam) / (2 * q lam) * p lam Y * rho := by
  have hp := p_pos lam Y hlam
  have hq := q_pos lam hlam
  have hrhop := feasible_vacancy_pos lam Y rho hlam hrho
  have hb := heavy_parent_probability_bound lam Y hlam hx
  have ht : (1 + q lam) * (p lam Y * rho) ≤ q lam := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (1 + q lam) * p lam Y)
      (sub_nonneg.mpr hrho.2)]
  have hw : q lam ≤ (1 + q lam) * ((1 - p lam Y * rho) * q lam) := by
    nlinarith [mul_nonneg hq.le (sub_nonneg.mpr ht)]
  unfold source
  rw [heavy_child_cap lam Y hlam hx, feasible_source_max lam Y rho hlam hrho,
    f_first_branch lam _ hlam ht, f_second_branch lam _ hlam hw]
  field_simp
  <;> ring

end F4Heavy.Analysis
