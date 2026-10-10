module

public import Erdos993Lean.BCFG.LogIntegerMidpointsBC
public import Erdos993Lean.BCFG.LogIntegerMidpointsFG
public import Erdos993Lean.BCFG.LogIntegerMass

/-! Exact printed midpoint brackets and four mass logarithm bounds.
These consume only the twelve finite tests and the generic real logarithm theorem. -/

@[expose] public section
set_option autoImplicit false

namespace Erdos993Lean.BCFG.Analytic.NatLog

theorem midpoint_B_log :
    (52472852 : ℝ)/10^8 < Real.log (169/100) ∧
      Real.log (169/100) < (52472853 : ℝ)/10^8 := by
  have he : (1+(69 : ℝ)/269)/(1-69/269) = 169/100 := by norm_num
  constructor
  · rw [← he]
    exact midpoint_B_lower_series.trans (logLower_lt 12 (by norm_num) (by norm_num))
  · rw [← he]
    exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans midpoint_B_upper_series

theorem midpoint_C_log :
    (58221561 : ℝ)/10^8 < Real.log (179/100) ∧
      Real.log (179/100) < (58221562 : ℝ)/10^8 := by
  have he : (1+(79 : ℝ)/279)/(1-79/279) = 179/100 := by norm_num
  constructor
  · rw [← he]
    exact midpoint_C_lower_series.trans (logLower_lt 12 (by norm_num) (by norm_num))
  · rw [← he]
    exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans midpoint_C_upper_series

theorem midpoint_F_log :
    (96508089 : ℝ)/10^8 < Real.log (21/8) ∧
      Real.log (21/8) < (96508090 : ℝ)/10^8 := by
  have he : (1+(13 : ℝ)/29)/(1-13/29) = 21/8 := by norm_num
  constructor
  · rw [← he]
    exact midpoint_F_lower_series.trans (logLower_lt 12 (by norm_num) (by norm_num))
  · rw [← he]
    exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans midpoint_F_upper_series

theorem midpoint_G_log :
    (99325177 : ℝ)/10^8 < Real.log (27/10) ∧
      Real.log (27/10) < (99325178 : ℝ)/10^8 := by
  have he : (1+(17 : ℝ)/37)/(1-17/37) = 27/10 := by norm_num
  constructor
  · rw [← he]
    exact midpoint_G_lower_series.trans (logLower_lt 12 (by norm_num) (by norm_num))
  · rw [← he]
    exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans midpoint_G_upper_series

theorem mass_three_fifths_log : Real.log (8/5 : ℝ) < 150/319 := by
  have he : (1+(3 : ℝ)/13)/(1-3/13) = 8/5 := by norm_num
  rw [← he]
  exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans mass_three_fifths_series

theorem mass_four_fifths_log : Real.log (9/5 : ℝ) < 1600/2721 := by
  have he : (1+(2 : ℝ)/7)/(1-2/7) = 9/5 := by norm_num
  rw [← he]
  exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans mass_four_fifths_series

theorem mass_eight_fifths_log : Real.log (13/5 : ℝ) < 672/703 := by
  have he : (1+(4 : ℝ)/9)/(1-4/9) = 13/5 := by norm_num
  rw [← he]
  exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans mass_eight_fifths_series

theorem mass_seven_fourths_log : Real.log (11/4 : ℝ) < 84/83 := by
  have he : (1+(7 : ℝ)/15)/(1-7/15) = 11/4 := by norm_num
  rw [← he]
  exact (log_lt_logUpper 12 (by norm_num) (by norm_num)).trans mass_seven_fourths_series

end Erdos993Lean.BCFG.Analytic.NatLog

#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_B_log
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_C_log
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_F_log
#check Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.midpoint_G_log
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_three_fifths_log
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_four_fifths_log
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_eight_fifths_log
#check Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_log
#print axioms Erdos993Lean.BCFG.Analytic.NatLog.mass_seven_fourths_log
