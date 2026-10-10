module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict027

def records : List Comparison := [
  -- P024.lower; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats ((2940636 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P024.upper; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((2940642 : Rat)/10000000) .lt,
  -- P025.lower; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats ((2710003 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))))) .lt,
  -- P025.upper; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))))) ((2710008 : Rat)/10000000) .lt,
  -- P026.lower; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats ((2495280 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P026.upper; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((2495285 : Rat)/10000000) .lt,
  -- P027.lower; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats ((2295680 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))))) .lt,
  -- P027.upper; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))))) ((2295685 : Rat)/10000000) .lt,
  -- P028.lower; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats ((2110411 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P028.upper; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((2110415 : Rat)/10000000) .lt,
  -- P029.lower; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats ((1779715 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P029.upper; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((1779718 : Rat)/10000000) .lt,
  -- P030.lower; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats ((1497016 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P030.upper; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((1497019 : Rat)/10000000) .lt,
  -- P031.lower; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats ((1256435 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P031.upper; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (5 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((1256439 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict027
