module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict051

def records : List Comparison := [
  -- P216.lower; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats ((3689808 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P216.upper; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((44816889 : Rat) / (10000000 : Rat))))))) ((3689813 : Rat)/10000000) .lt,
  -- P217.lower; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats ((3147833 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P217.upper; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((1689359 : Rat) / (312500 : Rat))))))) ((3147838 : Rat)/10000000) .lt,
  -- P218.lower; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats ((2675121 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P218.upper; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((6520819 : Rat) / (1000000 : Rat))))))) ((2675127 : Rat)/10000000) .lt,
  -- P219.lower; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats ((2265545 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P219.upper; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((78656091 : Rat) / (10000000 : Rat))))))) ((2265551 : Rat)/10000000) .lt,
  -- P220.lower; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats ((1912797 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P220.upper; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((94877357 : Rat) / (10000000 : Rat))))))) ((1912802 : Rat)/10000000) .lt,
  -- P221.lower; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats ((1352990 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P221.upper; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((6902287 : Rat) / (500000 : Rat))))))) ((1352996 : Rat)/10000000) .lt,
  -- P222.lower; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats ((949223 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P222.upper; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((40171073 : Rat) / (2000000 : Rat))))))) ((949231 : Rat)/10000000) .lt,
  -- P223.lower; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats ((10021959 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6766189 : Rat) / (5000000 : Rat))))))) .lt,
  -- P223.upper; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((108259 : Rat) / (80000 : Rat))))))) ((10021971 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict051
