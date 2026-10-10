module

public import F4Heavy.Analysis.LogSeriesRemainder

@[expose] public section
set_option autoImplicit false

namespace F4Heavy.Analysis

/-- Independent analytic enclosure, without importing a numerical certificate. -/
theorem cap_log_five_halves_upper : Real.log (5 / 2 : ℝ) < 11 / 12 := by
  have h := log_series_tight_upper 6 (3 / 7 : ℝ) (by norm_num) (by norm_num)
  norm_num [Finset.sum_range_succ] at h
  linarith only [h]

end F4Heavy.Analysis
