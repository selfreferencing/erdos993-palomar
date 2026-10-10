module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict006

def records : List Comparison := [
  -- E005.lower; E005: 12348350/10000000 < E_minus(27/128); E_plus(27/128) < 12348353/10000000.
  Comparison.ofRats ((12348350 : Rat)/10000000) ((expLower (((27 : Rat) / (128 : Rat))))) .lt,
  -- E005.upper; E005: 12348350/10000000 < E_minus(27/128); E_plus(27/128) < 12348353/10000000.
  Comparison.ofRats ((expUpper (((27 : Rat) / (128 : Rat))))) ((12348353 : Rat)/10000000) .lt,
  -- E006.lower; E006: 12641183/10000000 < E_minus(15/64); E_plus(15/64) < 12641186/10000000.
  Comparison.ofRats ((12641183 : Rat)/10000000) ((expLower (((15 : Rat) / (64 : Rat))))) .lt,
  -- E006.upper; E006: 12641183/10000000 < E_minus(15/64); E_plus(15/64) < 12641186/10000000.
  Comparison.ofRats ((expUpper (((15 : Rat) / (64 : Rat))))) ((12641186 : Rat)/10000000) .lt,
  -- E007.lower; E007: 12940960/10000000 < E_minus(33/128); E_plus(33/128) < 12940963/10000000.
  Comparison.ofRats ((12940960 : Rat)/10000000) ((expLower (((33 : Rat) / (128 : Rat))))) .lt,
  -- E007.upper; E007: 12940960/10000000 < E_minus(33/128); E_plus(33/128) < 12940963/10000000.
  Comparison.ofRats ((expUpper (((33 : Rat) / (128 : Rat))))) ((12940963 : Rat)/10000000) .lt,
  -- E008.lower; E008: 13247846/10000000 < E_minus(9/32); E_plus(9/32) < 13247849/10000000.
  Comparison.ofRats ((13247846 : Rat)/10000000) ((expLower (((9 : Rat) / (32 : Rat))))) .lt,
  -- E008.upper; E008: 13247846/10000000 < E_minus(9/32); E_plus(9/32) < 13247849/10000000.
  Comparison.ofRats ((expUpper (((9 : Rat) / (32 : Rat))))) ((13247849 : Rat)/10000000) .lt,
  -- E009.lower; E009: 13532375/10000000 < E_minus(121/400); E_plus(121/400) < 13532378/10000000.
  Comparison.ofRats ((13532375 : Rat)/10000000) ((expLower (((121 : Rat) / (400 : Rat))))) .lt,
  -- E009.upper; E009: 13532375/10000000 < E_minus(121/400); E_plus(121/400) < 13532378/10000000.
  Comparison.ofRats ((expUpper (((121 : Rat) / (400 : Rat))))) ((13532378 : Rat)/10000000) .lt,
  -- E010.lower; E010: 13562010/10000000 < E_minus(39/128); E_plus(39/128) < 13562013/10000000.
  Comparison.ofRats ((13562010 : Rat)/10000000) ((expLower (((39 : Rat) / (128 : Rat))))) .lt,
  -- E010.upper; E010: 13562010/10000000 < E_minus(39/128); E_plus(39/128) < 13562013/10000000.
  Comparison.ofRats ((expUpper (((39 : Rat) / (128 : Rat))))) ((13562013 : Rat)/10000000) .lt,
  -- E011.lower; E011: 13883624/10000000 < E_minus(21/64); E_plus(21/64) < 13883627/10000000.
  Comparison.ofRats ((13883624 : Rat)/10000000) ((expLower (((21 : Rat) / (64 : Rat))))) .lt,
  -- E011.upper; E011: 13883624/10000000 < E_minus(21/64); E_plus(21/64) < 13883627/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (64 : Rat))))) ((13883627 : Rat)/10000000) .lt,
  -- E012.lower; E012: 14212864/10000000 < E_minus(45/128); E_plus(45/128) < 14212867/10000000.
  Comparison.ofRats ((14212864 : Rat)/10000000) ((expLower (((45 : Rat) / (128 : Rat))))) .lt,
  -- E012.upper; E012: 14212864/10000000 < E_minus(45/128); E_plus(45/128) < 14212867/10000000.
  Comparison.ofRats ((expUpper (((45 : Rat) / (128 : Rat))))) ((14212867 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict006
