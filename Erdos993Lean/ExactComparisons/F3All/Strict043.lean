module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict043

def records : List Comparison := [
  -- P152.lower; P152: lambda=263/200, y=27/16: 2177291/10000000 < L_minus(1+(263/200)/(6757437/1250000)); L_plus(1+(263/200)/(1689359/312500)) < 2177295/10000000.
  Comparison.ofRats ((2177291 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P152.upper; P152: lambda=263/200, y=27/16: 2177291/10000000 < L_minus(1+(263/200)/(6757437/1250000)); L_plus(1+(263/200)/(1689359/312500)) < 2177295/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((2177295 : Rat)/10000000) .lt,
  -- P153.lower; P153: lambda=263/200, y=57/32: 2000648/10000000 < L_minus(1+(263/200)/(59372743/10000000)); L_plus(1+(263/200)/(14843183/2500000)) < 2000651/10000000.
  Comparison.ofRats ((2000648 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((59372743 : Rat) / (10000000 : Rat))))))) .lt,
  -- P153.upper; P153: lambda=263/200, y=57/32: 2000648/10000000 < L_minus(1+(263/200)/(59372743/10000000)); L_plus(1+(263/200)/(14843183/2500000)) < 2000651/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((14843183 : Rat) / (2500000 : Rat))))))) ((2000651 : Rat)/10000000) .lt,
  -- P154.lower; P154: lambda=263/200, y=15/8: 1837052/10000000 < L_minus(1+(263/200)/(32604103/5000000)); L_plus(1+(263/200)/(6520819/1000000)) < 1837056/10000000.
  Comparison.ofRats ((1837052 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P154.upper; P154: lambda=263/200, y=15/8: 1837052/10000000 < L_minus(1+(263/200)/(32604103/5000000)); L_plus(1+(263/200)/(6520819/1000000)) < 1837056/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((1837056 : Rat)/10000000) .lt,
  -- P155.lower; P155: lambda=263/200, y=63/32: 1685732/10000000 < L_minus(1+(263/200)/(71617209/10000000)); L_plus(1+(263/200)/(35808593/5000000)) < 1685736/10000000.
  Comparison.ofRats ((1685732 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((71617209 : Rat) / (10000000 : Rat))))))) .lt,
  -- P155.upper; P155: lambda=263/200, y=63/32: 1685732/10000000 < L_minus(1+(263/200)/(71617209/10000000)); L_plus(1+(263/200)/(35808593/5000000)) < 1685736/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((35808593 : Rat) / (5000000 : Rat))))))) ((1685736 : Rat)/10000000) .lt,
  -- P156.lower; P156: lambda=263/200, y=33/16: 1545934/10000000 < L_minus(1+(263/200)/(629249/80000)); L_plus(1+(263/200)/(78656091/10000000)) < 1545937/10000000.
  Comparison.ofRats ((1545934 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P156.upper; P156: lambda=263/200, y=33/16: 1545934/10000000 < L_minus(1+(263/200)/(629249/80000)); L_plus(1+(263/200)/(78656091/10000000)) < 1545937/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((1545937 : Rat)/10000000) .lt,
  -- P157.lower; P157: lambda=263/200, y=9/4: 1297992/10000000 < L_minus(1+(263/200)/(23719357/2500000)); L_plus(1+(263/200)/(94877357/10000000)) < 1297996/10000000.
  Comparison.ofRats ((1297992 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P157.upper; P157: lambda=263/200, y=9/4: 1297992/10000000 < L_minus(1+(263/200)/(23719357/2500000)); L_plus(1+(263/200)/(94877357/10000000)) < 1297996/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((1297996 : Rat)/10000000) .lt,
  -- P158.lower; P158: lambda=263/200, y=21/8: 909899/10000000 < L_minus(1+(263/200)/(27609207/2000000)); L_plus(1+(263/200)/(6902287/500000)) < 909904/10000000.
  Comparison.ofRats ((909899 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P158.upper; P158: lambda=263/200, y=21/8: 909899/10000000 < L_minus(1+(263/200)/(27609207/2000000)); L_plus(1+(263/200)/(6902287/500000)) < 909904/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((909904 : Rat)/10000000) .lt,
  -- P159.lower; P159: lambda=263/200, y=3: 634155/10000000 < L_minus(1+(263/200)/(100428229/5000000)); L_plus(1+(263/200)/(40171073/2000000)) < 634162/10000000.
  Comparison.ofRats ((634155 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P159.upper; P159: lambda=263/200, y=3: 634155/10000000 < L_minus(1+(263/200)/(100428229/5000000)); L_plus(1+(263/200)/(40171073/2000000)) < 634162/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((634162 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict043
