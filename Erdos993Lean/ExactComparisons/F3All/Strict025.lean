module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict025

def records : List Comparison := [
  -- P008.lower; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats ((1462239 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P008.upper; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((1462242 : Rat)/10000000) .lt,
  -- P009.lower; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats ((1226910 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P009.upper; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((1226913 : Rat)/10000000) .lt,
  -- P010.lower; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats ((1027527 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P010.upper; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((1027530 : Rat)/10000000) .lt,
  -- P011.lower; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats ((859165 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P011.upper; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((859168 : Rat)/10000000) .lt,
  -- P012.lower; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats ((717405 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P012.upper; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((717409 : Rat)/10000000) .lt,
  -- P013.lower; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats ((498545 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P013.upper; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((498548 : Rat)/10000000) .lt,
  -- P014.lower; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats ((345298 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P014.upper; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((345301 : Rat)/10000000) .lt,
  -- P015.lower; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats ((164592 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P015.upper; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((164596 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict025
