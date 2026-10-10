module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict028

def records : List Comparison := [
  -- P032.lower; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats ((1052503 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P032.upper; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((1052506 : Rat)/10000000) .lt,
  -- P033.lower; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats ((880226 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P033.upper; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((880229 : Rat)/10000000) .lt,
  -- P034.lower; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats ((613202 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P034.upper; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((613206 : Rat)/10000000) .lt,
  -- P035.lower; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats ((294344 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P035.upper; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((294349 : Rat)/10000000) .lt,
  -- P036.lower; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats ((5454589 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((376947 : Rat) / (312500 : Rat))))))) .lt,
  -- P036.upper; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))))) ((5454595 : Rat)/10000000) .lt,
  -- P037.lower; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats ((5071092 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))))) .lt,
  -- P037.upper; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))))) ((5071098 : Rat)/10000000) .lt,
  -- P038.lower; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats ((4887262 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((13883627 : Rat) / (10000000 : Rat))))))) .lt,
  -- P038.upper; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((1735453 : Rat) / (1250000 : Rat))))))) ((4887268 : Rat)/10000000) .lt,
  -- P039.lower; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats ((4708643 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P039.upper; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((4708649 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict028
