module

public import Erdos993Lean.BCFG.LogPairFormulas

/-! Four printed n=12 midpoint tests for B/C. Kernel decisions remain unexecuted. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

theorem midpoint_B_lower_nat :
    52472852*(lower 69 269 12).2 < (lower 69 269 12).1*10^8 := by decide +kernel
theorem midpoint_B_upper_nat :
    (upper 69 269 12).1*10^8 < 52472853*(upper 69 269 12).2 := by decide +kernel
theorem midpoint_C_lower_nat :
    58221561*(lower 79 279 12).2 < (lower 79 279 12).1*10^8 := by decide +kernel
theorem midpoint_C_upper_nat :
    (upper 79 279 12).1*10^8 < 58221562*(upper 79 279 12).2 := by decide +kernel

theorem midpoint_B_lower_series :
    (52472852 : ℝ)/10^8 < logLower 12 ((69 : ℝ)/269) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    lower_gt_rat_of_cross 12 69 269 52472852 (10^8) (by decide) (by decide)
      midpoint_B_lower_nat

theorem midpoint_B_upper_series :
    logUpper 12 ((69 : ℝ)/269) < (52472853 : ℝ)/10^8 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 69 269 52472853 (10^8) (by decide) (by decide)
      midpoint_B_upper_nat

theorem midpoint_C_lower_series :
    (58221561 : ℝ)/10^8 < logLower 12 ((79 : ℝ)/279) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    lower_gt_rat_of_cross 12 79 279 58221561 (10^8) (by decide) (by decide)
      midpoint_C_lower_nat

theorem midpoint_C_upper_series :
    logUpper 12 ((79 : ℝ)/279) < (58221562 : ℝ)/10^8 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 79 279 58221562 (10^8) (by decide) (by decide)
      midpoint_C_upper_nat

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_lower_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_lower_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_upper_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_upper_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_lower_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_lower_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_upper_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_upper_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_lower_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_lower_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_upper_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_upper_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_lower_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_lower_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_upper_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_upper_series
