module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict046

def records : List Comparison := [
  -- P176.lower; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats ((2887027 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P176.upper; P176: lambda=3/2, y=3/2: 2887027/10000000 < L_minus(1+(3/2)/(22408447/5000000)); L_plus(1+(3/2)/(44816889/10000000)) < 2887032/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((2887032 : Rat)/10000000) .lt,
  -- P177.lower; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats ((2448829 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P177.upper; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((2448834 : Rat)/10000000) .lt,
  -- P178.lower; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats ((2070403 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P178.upper; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((2070407 : Rat)/10000000) .lt,
  -- P179.lower; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats ((1745442 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P179.upper; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((1745445 : Rat)/10000000) .lt,
  -- P180.lower; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats ((1467795 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P180.upper; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((1467799 : Rat)/10000000) .lt,
  -- P181.lower; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats ((1031514 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P181.upper; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((1031519 : Rat)/10000000) .lt,
  -- P182.lower; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats ((720230 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P182.upper; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((720237 : Rat)/10000000) .lt,
  -- P183.lower; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats ((7897087 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P183.upper; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((7897096 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict046
