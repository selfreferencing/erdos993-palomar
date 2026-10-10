module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict048

def records : List Comparison := [
  -- P192.lower; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats ((4892183 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((27731949 : Rat) / (10000000 : Rat))))))) .lt,
  -- P192.upper; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((13865973 : Rat) / (5000000 : Rat))))))) ((4892188 : Rat)/10000000) .lt,
  -- P193.lower; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats ((4498911 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P193.upper; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((4498916 : Rat)/10000000) .lt,
  -- P194.lower; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats ((3859463 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P194.upper; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((3859468 : Rat)/10000000) .lt,
  -- P195.lower; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats ((3296471 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P195.upper; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((3296476 : Rat)/10000000) .lt,
  -- P196.lower; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats ((2804437 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P196.upper; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((2804442 : Rat)/10000000) .lt,
  -- P197.lower; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats ((2377332 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P197.upper; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((2377338 : Rat)/10000000) .lt,
  -- P198.lower; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats ((2008875 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P198.upper; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((2008879 : Rat)/10000000) .lt,
  -- P199.lower; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats ((1692771 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P199.upper; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((1692775 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict048
