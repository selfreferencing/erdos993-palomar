module

public import Erdos993Lean.BCFG.LogPairFormulas

/-! Four printed mass-endpoint n=12 tests. Every comparison is a Nat cross product. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

theorem mass_three_fifths_nat :
    (upper 3 13 12).1*319 < 150*(upper 3 13 12).2 := by decide +kernel
theorem mass_four_fifths_nat :
    (upper 2 7 12).1*2721 < 1600*(upper 2 7 12).2 := by decide +kernel
theorem mass_eight_fifths_nat :
    (upper 4 9 12).1*703 < 672*(upper 4 9 12).2 := by decide +kernel
theorem mass_seven_fourths_nat :
    (upper 7 15 12).1*83 < 84*(upper 7 15 12).2 := by decide +kernel

theorem mass_three_fifths_series : logUpper 12 ((3 : ℝ)/13) < (150 : ℝ)/319 := by
  simpa only [Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 3 13 150 319 (by decide) (by decide) mass_three_fifths_nat

theorem mass_four_fifths_series : logUpper 12 ((2 : ℝ)/7) < (1600 : ℝ)/2721 := by
  simpa only [Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 2 7 1600 2721 (by decide) (by decide) mass_four_fifths_nat

theorem mass_eight_fifths_series : logUpper 12 ((4 : ℝ)/9) < (672 : ℝ)/703 := by
  simpa only [Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 4 9 672 703 (by decide) (by decide) mass_eight_fifths_nat

theorem mass_seven_fourths_series : logUpper 12 ((7 : ℝ)/15) < (84 : ℝ)/83 := by
  simpa only [Nat.cast_ofNat] using
    upper_lt_rat_of_cross 12 7 15 84 83 (by decide) (by decide) mass_seven_fourths_nat

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_nat
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_nat
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_series
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_series
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_series
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_series
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_series
