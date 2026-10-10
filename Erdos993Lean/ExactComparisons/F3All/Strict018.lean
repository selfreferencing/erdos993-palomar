module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict018

def records : List Comparison := [
  -- E101.lower; E101: 30041659/10000000 < E_minus(11/10); E_plus(11/10) < 30041662/10000000.
  Comparison.ofRats ((30041659 : Rat)/10000000) ((expLower (((11 : Rat) / (10 : Rat))))) .lt,
  -- E101.upper; E101: 30041659/10000000 < E_minus(11/10); E_plus(11/10) < 30041662/10000000.
  Comparison.ofRats ((expUpper (((11 : Rat) / (10 : Rat))))) ((30041662 : Rat)/10000000) .lt,
  -- E102.lower; E102: 30088636/10000000 < E_minus(141/128); E_plus(141/128) < 30088639/10000000.
  Comparison.ofRats ((30088636 : Rat)/10000000) ((expLower (((141 : Rat) / (128 : Rat))))) .lt,
  -- E102.upper; E102: 30088636/10000000 < E_minus(141/128); E_plus(141/128) < 30088639/10000000.
  Comparison.ofRats ((expUpper (((141 : Rat) / (128 : Rat))))) ((30088639 : Rat)/10000000) .lt,
  -- E103.lower; E103: 30802167/10000000 < E_minus(9/8); E_plus(9/8) < 30802170/10000000.
  Comparison.ofRats ((30802167 : Rat)/10000000) ((expLower (((9 : Rat) / (8 : Rat))))) .lt,
  -- E103.upper; E103: 30802167/10000000 < E_minus(9/8); E_plus(9/8) < 30802170/10000000.
  Comparison.ofRats ((expUpper (((9 : Rat) / (8 : Rat))))) ((30802170 : Rat)/10000000) .lt,
  -- E104.lower; E104: 31532619/10000000 < E_minus(147/128); E_plus(147/128) < 31532623/10000000.
  Comparison.ofRats ((31532619 : Rat)/10000000) ((expLower (((147 : Rat) / (128 : Rat))))) .lt,
  -- E104.upper; E104: 31532619/10000000 < E_minus(147/128); E_plus(147/128) < 31532623/10000000.
  Comparison.ofRats ((expUpper (((147 : Rat) / (128 : Rat))))) ((31532623 : Rat)/10000000) .lt,
  -- E105.lower; E105: 32280394/10000000 < E_minus(75/64); E_plus(75/64) < 32280397/10000000.
  Comparison.ofRats ((32280394 : Rat)/10000000) ((expLower (((75 : Rat) / (64 : Rat))))) .lt,
  -- E105.upper; E105: 32280394/10000000 < E_minus(75/64); E_plus(75/64) < 32280397/10000000.
  Comparison.ofRats ((expUpper (((75 : Rat) / (64 : Rat))))) ((32280397 : Rat)/10000000) .lt,
  -- E106.lower; E106: 33045901/10000000 < E_minus(153/128); E_plus(153/128) < 33045905/10000000.
  Comparison.ofRats ((33045901 : Rat)/10000000) ((expLower (((153 : Rat) / (128 : Rat))))) .lt,
  -- E106.upper; E106: 33045901/10000000 < E_minus(153/128); E_plus(153/128) < 33045905/10000000.
  Comparison.ofRats ((expUpper (((153 : Rat) / (128 : Rat))))) ((33045905 : Rat)/10000000) .lt,
  -- E107.lower; E107: 33534845/10000000 < E_minus(121/100); E_plus(121/100) < 33534848/10000000.
  Comparison.ofRats ((33534845 : Rat)/10000000) ((expLower (((121 : Rat) / (100 : Rat))))) .lt,
  -- E107.upper; E107: 33534845/10000000 < E_minus(121/100); E_plus(121/100) < 33534848/10000000.
  Comparison.ofRats ((expUpper (((121 : Rat) / (100 : Rat))))) ((33534848 : Rat)/10000000) .lt,
  -- E108.lower; E108: 33829562/10000000 < E_minus(39/32); E_plus(39/32) < 33829566/10000000.
  Comparison.ofRats ((33829562 : Rat)/10000000) ((expLower (((39 : Rat) / (32 : Rat))))) .lt,
  -- E108.upper; E108: 33829562/10000000 < E_minus(39/32); E_plus(39/32) < 33829566/10000000.
  Comparison.ofRats ((expUpper (((39 : Rat) / (32 : Rat))))) ((33829566 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict018
