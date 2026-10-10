module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict030

def records : List Comparison := [
  -- P048.lower; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats ((3324592 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((22185971 : Rat) / (10000000 : Rat))))))) .lt,
  -- P048.upper; P048: lambda=7/8, y=51/64: 3324592/10000000 < L_minus(1+(7/8)/(22185971/10000000)); L_plus(1+(7/8)/(1386623/625000)) < 3324597/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((1386623 : Rat) / (625000 : Rat))))))) ((3324597 : Rat)/10000000) .lt,
  -- P049.lower; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats ((3194223 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((11625349 : Rat) / (5000000 : Rat))))))) .lt,
  -- P049.upper; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((4650139 : Rat) / (2000000 : Rat))))))) ((3194228 : Rat)/10000000) .lt,
  -- P050.lower; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats ((2946486 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P050.upper; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((2946492 : Rat)/10000000) .lt,
  -- P051.lower; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats ((2715454 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((5609139 : Rat) / (2000000 : Rat))))))) .lt,
  -- P051.upper; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((7011423 : Rat) / (2500000 : Rat))))))) ((2715459 : Rat)/10000000) .lt,
  -- P052.lower; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats ((2500351 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P052.upper; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((2500356 : Rat)/10000000) .lt,
  -- P053.lower; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats ((2300390 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((16914783 : Rat) / (5000000 : Rat))))))) .lt,
  -- P053.upper; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((16914781 : Rat) / (5000000 : Rat))))))) ((2300395 : Rat)/10000000) .lt,
  -- P054.lower; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats ((2114780 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P054.upper; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((2114784 : Rat)/10000000) .lt,
  -- P055.lower; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats ((1942730 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((20403123 : Rat) / (5000000 : Rat))))))) .lt,
  -- P055.upper; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((20403121 : Rat) / (5000000 : Rat))))))) ((1942733 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict030
