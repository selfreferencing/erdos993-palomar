module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict053

def records : List Comparison := [
  -- P232.lower; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats ((6866992 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((5909287 : Rat) / (2500000 : Rat))))))) .lt,
  -- P232.upper; P232: lambda=7/3, y=11011/12800: 6866992/10000000 < L_minus(1+(7/3)/(5909287/2500000)); L_plus(1+(7/3)/(4727429/2000000)) < 6867001/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((4727429 : Rat) / (2000000 : Rat))))))) ((6867001 : Rat)/10000000) .lt,
  -- P233.lower; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats ((6820145 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((5965413 : Rat) / (2500000 : Rat))))))) .lt,
  -- P233.upper; P233: lambda=7/3, y=2783/3200: 6820145/10000000 < L_minus(1+(7/3)/(5965413/2500000)); L_plus(1+(7/3)/(23861649/10000000)) < 6820153/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((23861649 : Rat) / (10000000 : Rat))))))) ((6820153 : Rat)/10000000) .lt,
  -- P234.lower; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats ((6773520 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((24088289 : Rat) / (10000000 : Rat))))))) .lt,
  -- P234.upper; P234: lambda=7/3, y=11253/12800: 6773520/10000000 < L_minus(1+(7/3)/(24088289/10000000)); L_plus(1+(7/3)/(12044143/5000000)) < 6773528/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((12044143 : Rat) / (5000000 : Rat))))))) ((6773528 : Rat)/10000000) .lt,
  -- P235.lower; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats ((6727119 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((12158539 : Rat) / (5000000 : Rat))))))) .lt,
  -- P235.upper; P235: lambda=7/3, y=5687/6400: 6727119/10000000 < L_minus(1+(7/3)/(12158539/5000000)); L_plus(1+(7/3)/(972683/400000)) < 6727127/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((972683 : Rat) / (400000 : Rat))))))) ((6727127 : Rat)/10000000) .lt,
  -- P236.lower; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats ((6634986 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6195299 : Rat) / (2500000 : Rat))))))) .lt,
  -- P236.upper; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((24781193 : Rat) / (10000000 : Rat))))))) ((6634994 : Rat)/10000000) .lt,
  -- P237.lower; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats ((6543746 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((25254173 : Rat) / (10000000 : Rat))))))) .lt,
  -- P237.upper; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((2525417 : Rat) / (1000000 : Rat))))))) ((6543753 : Rat)/10000000) .lt,
  -- P238.lower; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats ((6453398 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((25736177 : Rat) / (10000000 : Rat))))))) .lt,
  -- P238.upper; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((12868087 : Rat) / (5000000 : Rat))))))) ((6453405 : Rat)/10000000) .lt,
  -- P239.lower; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats ((6275376 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((13363979 : Rat) / (5000000 : Rat))))))) .lt,
  -- P239.upper; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((5345591 : Rat) / (2000000 : Rat))))))) ((6275382 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict053
