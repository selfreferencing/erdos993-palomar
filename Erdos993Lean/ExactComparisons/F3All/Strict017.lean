module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict017

def records : List Comparison := [
  -- E093.lower; E093: 26761386/10000000 < E_minus(63/64); E_plus(63/64) < 26761389/10000000.
  Comparison.ofRats ((26761386 : Rat)/10000000) ((expLower (((63 : Rat) / (64 : Rat))))) .lt,
  -- E093.upper; E093: 26761386/10000000 < E_minus(63/64); E_plus(63/64) < 26761389/10000000.
  Comparison.ofRats ((expUpper (((63 : Rat) / (64 : Rat))))) ((26761389 : Rat)/10000000) .lt,
  -- E094.lower; E094: 27396014/10000000 < E_minus(129/128); E_plus(129/128) < 27396017/10000000.
  Comparison.ofRats ((27396014 : Rat)/10000000) ((expLower (((129 : Rat) / (128 : Rat))))) .lt,
  -- E094.upper; E094: 27396014/10000000 < E_minus(129/128); E_plus(129/128) < 27396017/10000000.
  Comparison.ofRats ((expUpper (((129 : Rat) / (128 : Rat))))) ((27396017 : Rat)/10000000) .lt,
  -- E095.lower; E095: 27731946/10000000 < E_minus(51/50); E_plus(51/50) < 27731949/10000000.
  Comparison.ofRats ((27731946 : Rat)/10000000) ((expLower (((51 : Rat) / (50 : Rat))))) .lt,
  -- E095.upper; E095: 27731946/10000000 < E_minus(51/50); E_plus(51/50) < 27731949/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (50 : Rat))))) ((27731949 : Rat)/10000000) .lt,
  -- E096.lower; E096: 27757957/10000000 < E_minus(3267/3200); E_plus(3267/3200) < 27757960/10000000.
  Comparison.ofRats ((27757957 : Rat)/10000000) ((expLower (((3267 : Rat) / (3200 : Rat))))) .lt,
  -- E096.upper; E096: 27757957/10000000 < E_minus(3267/3200); E_plus(3267/3200) < 27757960/10000000.
  Comparison.ofRats ((expUpper (((3267 : Rat) / (3200 : Rat))))) ((27757960 : Rat)/10000000) .lt,
  -- E097.lower; E097: 28045692/10000000 < E_minus(33/32); E_plus(33/32) < 28045695/10000000.
  Comparison.ofRats ((28045692 : Rat)/10000000) ((expLower (((33 : Rat) / (32 : Rat))))) .lt,
  -- E097.upper; E097: 28045692/10000000 < E_minus(33/32); E_plus(33/32) < 28045695/10000000.
  Comparison.ofRats ((expUpper (((33 : Rat) / (32 : Rat))))) ((28045695 : Rat)/10000000) .lt,
  -- E098.lower; E098: 28710777/10000000 < E_minus(135/128); E_plus(135/128) < 28710780/10000000.
  Comparison.ofRats ((28710777 : Rat)/10000000) ((expLower (((135 : Rat) / (128 : Rat))))) .lt,
  -- E098.upper; E098: 28710777/10000000 < E_minus(135/128); E_plus(135/128) < 28710780/10000000.
  Comparison.ofRats ((expUpper (((135 : Rat) / (128 : Rat))))) ((28710780 : Rat)/10000000) .lt,
  -- E099.lower; E099: 28827651/10000000 < E_minus(847/800); E_plus(847/800) < 28827654/10000000.
  Comparison.ofRats ((28827651 : Rat)/10000000) ((expLower (((847 : Rat) / (800 : Rat))))) .lt,
  -- E099.upper; E099: 28827651/10000000 < E_minus(847/800); E_plus(847/800) < 28827654/10000000.
  Comparison.ofRats ((expUpper (((847 : Rat) / (800 : Rat))))) ((28827654 : Rat)/10000000) .lt,
  -- E100.lower; E100: 29391633/10000000 < E_minus(69/64); E_plus(69/64) < 29391636/10000000.
  Comparison.ofRats ((29391633 : Rat)/10000000) ((expLower (((69 : Rat) / (64 : Rat))))) .lt,
  -- E100.upper; E100: 29391633/10000000 < E_minus(69/64); E_plus(69/64) < 29391636/10000000.
  Comparison.ofRats ((expUpper (((69 : Rat) / (64 : Rat))))) ((29391636 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict017
