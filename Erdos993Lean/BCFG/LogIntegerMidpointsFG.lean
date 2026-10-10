module

public import Erdos993Lean.BCFG.LogPairFormulas

/-! Four printed n=12 midpoint tests for F/G. No large integer answers are stored. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

theorem midpoint_F_lower_nat :
    96508089*(lower 13 29 12).2 < (lower 13 29 12).1*10^8 := by decide +kernel
theorem midpoint_F_upper_nat :
    (upper 13 29 12).1*10^8 < 96508090*(upper 13 29 12).2 := by decide +kernel
theorem midpoint_G_lower_nat :
    99325177*(lower 17 37 12).2 < (lower 17 37 12).1*10^8 := by decide +kernel
theorem midpoint_G_upper_nat :
    (upper 17 37 12).1*10^8 < 99325178*(upper 17 37 12).2 := by decide +kernel

theorem midpoint_F_lower_series :
    (96508089 : ℝ)/10^8 < logLower 12 ((13 : ℝ)/29) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    lower_gt_rat_of_cross 12 13 29 96508089 (10^8) (by decide) (by decide)
      midpoint_F_lower_nat

theorem midpoint_F_upper_series :
    logUpper 12 ((13 : ℝ)/29) < (96508090 : ℝ)/10^8 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 13 29 96508090 (10^8) (by decide) (by decide)
      midpoint_F_upper_nat

theorem midpoint_G_lower_series :
    (99325177 : ℝ)/10^8 < logLower 12 ((17 : ℝ)/37) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    lower_gt_rat_of_cross 12 17 37 99325177 (10^8) (by decide) (by decide)
      midpoint_G_lower_nat

theorem midpoint_G_upper_series :
    logUpper 12 ((17 : ℝ)/37) < (99325178 : ℝ)/10^8 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 17 37 99325178 (10^8) (by decide) (by decide)
      midpoint_G_upper_nat

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_lower_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_lower_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_upper_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_upper_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_lower_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_lower_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_upper_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_upper_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_lower_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_lower_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_upper_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_upper_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_lower_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_lower_series
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_upper_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_upper_series
