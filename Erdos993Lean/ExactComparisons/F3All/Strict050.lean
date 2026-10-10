module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict050

def records : List Comparison := [
  -- P208.lower; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats ((6293920 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((22818809 : Rat) / (10000000 : Rat))))))) .lt,
  -- P208.upper; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((11409403 : Rat) / (5000000 : Rat))))))) ((6293926 : Rat)/10000000) .lt,
  -- P209.lower; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats ((6134829 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((23616843 : Rat) / (10000000 : Rat))))))) .lt,
  -- P209.upper; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((590421 : Rat) / (250000 : Rat))))))) ((6134835 : Rat)/10000000) .lt,
  -- P210.lower; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats ((5978672 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((24442787 : Rat) / (10000000 : Rat))))))) .lt,
  -- P210.upper; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((763837 : Rat) / (312500 : Rat))))))) ((5978678 : Rat)/10000000) .lt,
  -- P211.lower; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats ((5784155 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P211.upper; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((25535893 : Rat) / (10000000 : Rat))))))) ((5784161 : Rat)/10000000) .lt,
  -- P212.lower; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats ((5675121 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((1309117 : Rat) / (500000 : Rat))))))) .lt,
  -- P212.upper; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((26182337 : Rat) / (10000000 : Rat))))))) ((5675126 : Rat)/10000000) .lt,
  -- P213.lower; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats ((5102705 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((15020831 : Rat) / (5000000 : Rat))))))) .lt,
  -- P213.upper; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((30041659 : Rat) / (10000000 : Rat))))))) ((5102710 : Rat)/10000000) .lt,
  -- P214.lower; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats ((5003537 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P214.upper; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((30802167 : Rat) / (10000000 : Rat))))))) ((5003542 : Rat)/10000000) .lt,
  -- P215.lower; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats ((4306729 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P215.upper; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((18577253 : Rat) / (5000000 : Rat))))))) ((4306734 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict050
