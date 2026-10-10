module

public import F4Heavy.Contract
public import Mathlib.Tactic.NormNum

/-! The two strict logarithm comparisons used by the literal light h-minus
bounds. Finite rational exponential sums are checked here; the comparison
with the exponential is the proved Mathlib Taylor-series inequality. -/

@[expose] public section

namespace F4Unified.LightConstruction
open scoped BigOperators

 theorem exp_taylor_lower_24_25 :
    (13 : ℝ) / 5 < ∑ i ∈ Finset.range 5, ((24 : ℝ) / 25)^i / (i.factorial : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

 theorem log_13_5_lt_24_25 : Real.log ((13 : ℝ) / 5) < 24 / 25 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 13 / 5)).2
  exact exp_taylor_lower_24_25.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 5)

 theorem exp_taylor_lower_35_29 :
    (10 : ℝ) / 3 < ∑ i ∈ Finset.range 6, ((35 : ℝ) / 29)^i / (i.factorial : ℝ) := by
  norm_num [Finset.sum_range_succ, Nat.factorial]

 theorem log_10_3_lt_35_29 : Real.log ((10 : ℝ) / 3) < 35 / 29 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10 / 3)).2
  exact exp_taylor_lower_35_29.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 6)

#print axioms exp_taylor_lower_24_25
#print axioms log_13_5_lt_24_25
#print axioms exp_taylor_lower_35_29
#print axioms log_10_3_lt_35_29

end F4Unified.LightConstruction
