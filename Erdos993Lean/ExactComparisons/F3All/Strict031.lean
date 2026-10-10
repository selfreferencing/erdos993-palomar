module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict031

def records : List Comparison := [
  -- P056.lower; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats ((1783459 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P056.upper; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((1783462 : Rat)/10000000) .lt,
  -- P057.lower; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats ((1636201 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((4922173 : Rat) / (1000000 : Rat))))))) .lt,
  -- P057.upper; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((12305431 : Rat) / (2500000 : Rat))))))) ((1636205 : Rat)/10000000) .lt,
  -- P058.lower; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats ((1500209 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P058.upper; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((1500212 : Rat)/10000000) .lt,
  -- P059.lower; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats ((1259147 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P059.upper; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((1259150 : Rat)/10000000) .lt,
  -- P060.lower; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats ((1054797 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P060.upper; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((1054801 : Rat)/10000000) .lt,
  -- P061.lower; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats ((882161 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P061.upper; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((882164 : Rat)/10000000) .lt,
  -- P062.lower; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats ((614567 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P062.upper; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((614572 : Rat)/10000000) .lt,
  -- P063.lower; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats ((426411 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P063.upper; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((426416 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict031
