module

public import F4Heavy.Analysis.CapLogConstant
public import F4Heavy.Analysis.CapDomain

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis
open F4Unified

theorem cap_log_thirtythree_tenths_lower : (119 : ℝ) / 100 < Real.log (33 / 10) := by
  have h := Real.sum_range_le_log_div (show (0 : ℝ) ≤ 23 / 43 by norm_num)
    (show (23 : ℝ) / 43 < 1 by norm_num) 5
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

theorem cap_log_fortysix_thirtythirds_upper : Real.log (46 / 33 : ℝ) < 1 / 3 := by
  have h := log_series_tight_upper 4 (13 / 79 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

noncomputable def capReserveLogMargin (lam : ℝ) : ℝ :=
  lam / (1 + lam) * Real.log (lam + 2) - 2 * Real.log (2 * (lam + 1) / (lam + 2))

theorem cap_reserve_log_margin_derivative (lam : ℝ) (hl : 0 < lam) :
    HasDerivAt capReserveLogMargin
      ((Real.log (lam + 2) - 1) / (1 + lam) ^ 2 +
        lam ^ 2 / ((1 + lam) ^ 2 * (lam + 2))) lam := by
  have h1 : 1 + lam ≠ 0 := by positivity
  have h2 : lam + 2 ≠ 0 := by positivity
  have harg : 2 * (lam + 1) / (lam + 2) ≠ 0 := by positivity
  have hi := hasDerivAt_id lam
  have h := ((hi.div (hi.const_add 1) h1).mul ((hi.add_const 2).log h2)).sub
    ((((hi.add_const 1).const_mul 2).div (hi.add_const 2) h2).log harg |>.const_mul 2)
  convert h using 1
  · rfl
  · dsimp
    field_simp
    <;> ring

theorem cap_reserve_log_margin_monotone :
    MonotoneOn capReserveLogMargin (Set.Ici (13 / 10 : ℝ)) := by
  have hlog (lam : ℝ) (hl : 13 / 10 ≤ lam) : 1 < Real.log (lam + 2) := by
    have h := Real.log_le_log (show (0 : ℝ) < 33 / 10 by norm_num)
      (show (33 : ℝ) / 10 ≤ lam + 2 by linarith only [hl])
    linarith only [h, cap_log_thirtythree_tenths_lower]
  apply monotoneOn_of_deriv_nonneg (convex_Ici (13 / 10 : ℝ))
  · intro lam hl
    change 13 / 10 ≤ lam at hl
    exact (cap_reserve_log_margin_derivative lam (by linarith only [hl])).continuousAt.continuousWithinAt
  · intro lam hl
    have hl' : 13 / 10 ≤ lam := interior_subset hl
    exact (cap_reserve_log_margin_derivative lam (by linarith only [hl'])).differentiableAt.differentiableWithinAt
  · intro lam hl
    have hl' : 13 / 10 ≤ lam := interior_subset hl
    rw [(cap_reserve_log_margin_derivative lam (by linarith only [hl'])).deriv]
    have hg := sub_pos.mpr (hlog lam hl')
    have hp : 0 < lam := by linarith only [hl']
    positivity

theorem cap_reserve_log_margin_positive (lam : ℝ) (hl : 13 / 10 ≤ lam) :
    0 < capReserveLogMargin lam := by
  have he : 0 < capReserveLogMargin (13 / 10) := by
    norm_num [capReserveLogMargin]
    linarith only [cap_log_thirtythree_tenths_lower, cap_log_fortysix_thirtythirds_upper]
  exact he.trans_le (cap_reserve_log_margin_monotone (by simp) hl hl)

end F4Heavy.Analysis
