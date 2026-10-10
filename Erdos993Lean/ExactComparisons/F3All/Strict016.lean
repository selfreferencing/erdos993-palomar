module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict016

def records : List Comparison := [
  -- E085.lower; E085: 24944355/10000000 < E_minus(117/128); E_plus(117/128) < 24944358/10000000.
  Comparison.ofRats ((24944355 : Rat)/10000000) ((expLower (((117 : Rat) / (128 : Rat))))) .lt,
  -- E085.upper; E085: 24944355/10000000 < E_minus(117/128); E_plus(117/128) < 24944358/10000000.
  Comparison.ofRats ((expUpper (((117 : Rat) / (128 : Rat))))) ((24944358 : Rat)/10000000) .lt,
  -- E086.lower; E086: 25092902/10000000 < E_minus(23/25); E_plus(23/25) < 25092905/10000000.
  Comparison.ofRats ((25092902 : Rat)/10000000) ((expLower (((23 : Rat) / (25 : Rat))))) .lt,
  -- E086.upper; E086: 25092902/10000000 < E_minus(23/25); E_plus(23/25) < 25092905/10000000.
  Comparison.ofRats ((expUpper (((23 : Rat) / (25 : Rat))))) ((25092905 : Rat)/10000000) .lt,
  -- E087.lower; E087: 25254170/10000000 < E_minus(5929/6400); E_plus(5929/6400) < 25254173/10000000.
  Comparison.ofRats ((25254170 : Rat)/10000000) ((expLower (((5929 : Rat) / (6400 : Rat))))) .lt,
  -- E087.upper; E087: 25254170/10000000 < E_minus(5929/6400); E_plus(5929/6400) < 25254173/10000000.
  Comparison.ofRats ((expUpper (((5929 : Rat) / (6400 : Rat))))) ((25254173 : Rat)/10000000) .lt,
  -- E088.lower; E088: 25535893/10000000 < E_minus(15/16); E_plus(15/16) < 25535896/10000000.
  Comparison.ofRats ((25535893 : Rat)/10000000) ((expLower (((15 : Rat) / (16 : Rat))))) .lt,
  -- E088.upper; E088: 25535893/10000000 < E_minus(15/16); E_plus(15/16) < 25535896/10000000.
  Comparison.ofRats ((expUpper (((15 : Rat) / (16 : Rat))))) ((25535896 : Rat)/10000000) .lt,
  -- E089.lower; E089: 25736174/10000000 < E_minus(121/128); E_plus(121/128) < 25736177/10000000.
  Comparison.ofRats ((25736174 : Rat)/10000000) ((expLower (((121 : Rat) / (128 : Rat))))) .lt,
  -- E089.upper; E089: 25736174/10000000 < E_minus(121/128); E_plus(121/128) < 25736177/10000000.
  Comparison.ofRats ((expUpper (((121 : Rat) / (128 : Rat))))) ((25736177 : Rat)/10000000) .lt,
  -- E090.lower; E090: 26141459/10000000 < E_minus(123/128); E_plus(123/128) < 26141462/10000000.
  Comparison.ofRats ((26141459 : Rat)/10000000) ((expLower (((123 : Rat) / (128 : Rat))))) .lt,
  -- E090.upper; E090: 26141459/10000000 < E_minus(123/128); E_plus(123/128) < 26141462/10000000.
  Comparison.ofRats ((expUpper (((123 : Rat) / (128 : Rat))))) ((26141462 : Rat)/10000000) .lt,
  -- E091.lower; E091: 26182337/10000000 < E_minus(77/80); E_plus(77/80) < 26182340/10000000.
  Comparison.ofRats ((26182337 : Rat)/10000000) ((expLower (((77 : Rat) / (80 : Rat))))) .lt,
  -- E091.upper; E091: 26182337/10000000 < E_minus(77/80); E_plus(77/80) < 26182340/10000000.
  Comparison.ofRats ((expUpper (((77 : Rat) / (80 : Rat))))) ((26182340 : Rat)/10000000) .lt,
  -- E092.lower; E092: 26727955/10000000 < E_minus(1573/1600); E_plus(1573/1600) < 26727958/10000000.
  Comparison.ofRats ((26727955 : Rat)/10000000) ((expLower (((1573 : Rat) / (1600 : Rat))))) .lt,
  -- E092.upper; E092: 26727955/10000000 < E_minus(1573/1600); E_plus(1573/1600) < 26727958/10000000.
  Comparison.ofRats ((expUpper (((1573 : Rat) / (1600 : Rat))))) ((26727958 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict016
