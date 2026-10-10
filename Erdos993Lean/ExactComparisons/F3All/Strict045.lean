module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict045

def records : List Comparison := [
  -- P168.lower; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats ((4978264 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))))) .lt,
  -- P168.upper; P168: lambda=3/2, y=27/32: 4978264/10000000 < L_minus(1+(3/2)/(11625349/5000000)); L_plus(1+(3/2)/(4650139/2000000)) < 4978269/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))))) ((4978269 : Rat)/10000000) .lt,
  -- P169.lower; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats ((4686140 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((5018581 : Rat) / (2000000 : Rat))))))) .lt,
  -- P169.upper; P169: lambda=3/2, y=23/25: 4686140/10000000 < L_minus(1+(3/2)/(5018581/2000000)); L_plus(1+(3/2)/(12546451/5000000)) < 4686145/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((12546451 : Rat) / (5000000 : Rat))))))) ((4686145 : Rat)/10000000) .lt,
  -- P170.lower; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats ((4621025 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P170.upper; P170: lambda=3/2, y=15/16: 4621025/10000000 < L_minus(1+(3/2)/(3191987/1250000)); L_plus(1+(3/2)/(25535893/10000000)) < 4621030/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((4621030 : Rat)/10000000) .lt,
  -- P171.lower; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats ((4284268 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((5609139 : Rat) / (2000000 : Rat))))))) .lt,
  -- P171.upper; P171: lambda=3/2, y=33/32: 4284268/10000000 < L_minus(1+(3/2)/(5609139/2000000)); L_plus(1+(3/2)/(7011423/2500000)) < 4284274/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((7011423 : Rat) / (2500000 : Rat))))))) ((4284274 : Rat)/10000000) .lt,
  -- P172.lower; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats ((3967460 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P172.upper; P172: lambda=3/2, y=9/8: 3967460/10000000 < L_minus(1+(3/2)/(3080217/1000000)); L_plus(1+(3/2)/(30802167/10000000)) < 3967466/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((3967466 : Rat)/10000000) .lt,
  -- P173.lower; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats ((3670005 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((16914783 : Rat) / (5000000 : Rat))))))) .lt,
  -- P173.upper; P173: lambda=3/2, y=39/32: 3670005/10000000 < L_minus(1+(3/2)/(16914783/5000000)); L_plus(1+(3/2)/(16914781/5000000)) < 3670011/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((16914781 : Rat) / (5000000 : Rat))))))) ((3670011 : Rat)/10000000) .lt,
  -- P174.lower; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats ((3391252 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P174.upper; P174: lambda=3/2, y=21/16: 3391252/10000000 < L_minus(1+(3/2)/(37154509/10000000)); L_plus(1+(3/2)/(18577253/5000000)) < 3391257/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((3391257 : Rat)/10000000) .lt,
  -- P175.lower; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats ((3130503 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((20403123 : Rat) / (5000000 : Rat))))))) .lt,
  -- P175.upper; P175: lambda=3/2, y=45/32: 3130503/10000000 < L_minus(1+(3/2)/(20403123/5000000)); L_plus(1+(3/2)/(20403121/5000000)) < 3130509/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((20403121 : Rat) / (5000000 : Rat))))))) ((3130509 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict045
