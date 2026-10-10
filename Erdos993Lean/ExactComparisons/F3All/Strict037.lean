module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict037

def records : List Comparison := [
  -- P104.lower; P104: lambda=28/25, y=15/8: 1585046/10000000 < L_minus(1+(28/25)/(32604103/5000000)); L_plus(1+(28/25)/(6520819/1000000)) < 1585050/10000000.
  Comparison.ofRats ((1585046 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P104.upper; P104: lambda=28/25, y=15/8: 1585046/10000000 < L_minus(1+(28/25)/(32604103/5000000)); L_plus(1+(28/25)/(6520819/1000000)) < 1585050/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((1585050 : Rat)/10000000) .lt,
  -- P105.lower; P105: lambda=28/25, y=63/32: 1453003/10000000 < L_minus(1+(28/25)/(71617209/10000000)); L_plus(1+(28/25)/(35808593/5000000)) < 1453007/10000000.
  Comparison.ofRats ((1453003 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((71617209 : Rat) / (10000000 : Rat))))))) .lt,
  -- P105.upper; P105: lambda=28/25, y=63/32: 1453003/10000000 < L_minus(1+(28/25)/(71617209/10000000)); L_plus(1+(28/25)/(35808593/5000000)) < 1453007/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((35808593 : Rat) / (5000000 : Rat))))))) ((1453007 : Rat)/10000000) .lt,
  -- P106.lower; P106: lambda=28/25, y=33/16: 1331241/10000000 < L_minus(1+(28/25)/(629249/80000)); L_plus(1+(28/25)/(78656091/10000000)) < 1331245/10000000.
  Comparison.ofRats ((1331241 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P106.upper; P106: lambda=28/25, y=33/16: 1331241/10000000 < L_minus(1+(28/25)/(629249/80000)); L_plus(1+(28/25)/(78656091/10000000)) < 1331245/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((1331245 : Rat)/10000000) .lt,
  -- P107.lower; P107: lambda=28/25, y=9/4: 1115833/10000000 < L_minus(1+(28/25)/(23719357/2500000)); L_plus(1+(28/25)/(94877357/10000000)) < 1115837/10000000.
  Comparison.ofRats ((1115833 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P107.upper; P107: lambda=28/25, y=9/4: 1115833/10000000 < L_minus(1+(28/25)/(23719357/2500000)); L_plus(1+(28/25)/(94877357/10000000)) < 1115837/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((1115837 : Rat)/10000000) .lt,
  -- P108.lower; P108: lambda=28/25, y=21/8: 780088/10000000 < L_minus(1+(28/25)/(27609207/2000000)); L_plus(1+(28/25)/(6902287/500000)) < 780093/10000000.
  Comparison.ofRats ((780088 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P108.upper; P108: lambda=28/25, y=21/8: 780088/10000000 < L_minus(1+(28/25)/(27609207/2000000)); L_plus(1+(28/25)/(6902287/500000)) < 780093/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((780093 : Rat)/10000000) .lt,
  -- P109.lower; P109: lambda=28/25, y=3: 542619/10000000 < L_minus(1+(28/25)/(100428229/5000000)); L_plus(1+(28/25)/(40171073/2000000)) < 542625/10000000.
  Comparison.ofRats ((542619 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P109.upper; P109: lambda=28/25, y=3: 542619/10000000 < L_minus(1+(28/25)/(100428229/5000000)); L_plus(1+(28/25)/(40171073/2000000)) < 542625/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((542625 : Rat)/10000000) .lt,
  -- P110.lower; P110: lambda=263/200, y=3/8: 6438438/10000000 < L_minus(1+(263/200)/(3637479/2500000)); L_plus(1+(263/200)/(14549913/10000000)) < 6438445/10000000.
  Comparison.ofRats ((6438438 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P110.upper; P110: lambda=263/200, y=3/8: 6438438/10000000 < L_minus(1+(263/200)/(3637479/2500000)); L_plus(1+(263/200)/(14549913/10000000)) < 6438445/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((6438445 : Rat)/10000000) .lt,
  -- P111.lower; P111: lambda=263/200, y=21/50: 6227333/10000000 < L_minus(1+(263/200)/(15219617/10000000)); L_plus(1+(263/200)/(7609807/5000000)) < 6227339/10000000.
  Comparison.ofRats ((6227333 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15219617 : Rat) / (10000000 : Rat))))))) .lt,
  -- P111.upper; P111: lambda=263/200, y=21/50: 6227333/10000000 < L_minus(1+(263/200)/(15219617/10000000)); L_plus(1+(263/200)/(7609807/5000000)) < 6227339/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7609807 : Rat) / (5000000 : Rat))))))) ((6227339 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict037
