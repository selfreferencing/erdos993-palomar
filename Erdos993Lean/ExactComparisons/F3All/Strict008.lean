module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict008

def records : List Comparison := [
  -- E021.lower; E021: 16358907/10000000 < E_minus(63/128); E_plus(63/128) < 16358910/10000000.
  Comparison.ofRats ((16358907 : Rat)/10000000) ((expLower (((63 : Rat) / (128 : Rat))))) .lt,
  -- E021.upper; E021: 16358907/10000000 < E_minus(63/128); E_plus(63/128) < 16358910/10000000.
  Comparison.ofRats ((expUpper (((63 : Rat) / (128 : Rat))))) ((16358910 : Rat)/10000000) .lt,
  -- E022.lower; E022: 16551740/10000000 < E_minus(129/256); E_plus(129/256) < 16551743/10000000.
  Comparison.ofRats ((16551740 : Rat)/10000000) ((expLower (((129 : Rat) / (256 : Rat))))) .lt,
  -- E022.upper; E022: 16551740/10000000 < E_minus(129/256); E_plus(129/256) < 16551743/10000000.
  Comparison.ofRats ((expUpper (((129 : Rat) / (256 : Rat))))) ((16551743 : Rat)/10000000) .lt,
  -- E023.lower; E023: 16652910/10000000 < E_minus(51/100); E_plus(51/100) < 16652913/10000000.
  Comparison.ofRats ((16652910 : Rat)/10000000) ((expLower (((51 : Rat) / (100 : Rat))))) .lt,
  -- E023.upper; E023: 16652910/10000000 < E_minus(51/100); E_plus(51/100) < 16652913/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (100 : Rat))))) ((16652913 : Rat)/10000000) .lt,
  -- E024.lower; E024: 16746847/10000000 < E_minus(33/64); E_plus(33/64) < 16746850/10000000.
  Comparison.ofRats ((16746847 : Rat)/10000000) ((expLower (((33 : Rat) / (64 : Rat))))) .lt,
  -- E024.upper; E024: 16746847/10000000 < E_minus(33/64); E_plus(33/64) < 16746850/10000000.
  Comparison.ofRats ((expUpper (((33 : Rat) / (64 : Rat))))) ((16746850 : Rat)/10000000) .lt,
  -- E025.lower; E025: 16944254/10000000 < E_minus(135/256); E_plus(135/256) < 16944257/10000000.
  Comparison.ofRats ((16944254 : Rat)/10000000) ((expLower (((135 : Rat) / (256 : Rat))))) .lt,
  -- E025.upper; E025: 16944254/10000000 < E_minus(135/256); E_plus(135/256) < 16944257/10000000.
  Comparison.ofRats ((expUpper (((135 : Rat) / (256 : Rat))))) ((16944257 : Rat)/10000000) .lt,
  -- E026.lower; E026: 17143987/10000000 < E_minus(69/128); E_plus(69/128) < 17143990/10000000.
  Comparison.ofRats ((17143987 : Rat)/10000000) ((expLower (((69 : Rat) / (128 : Rat))))) .lt,
  -- E026.upper; E026: 17143987/10000000 < E_minus(69/128); E_plus(69/128) < 17143990/10000000.
  Comparison.ofRats ((expUpper (((69 : Rat) / (128 : Rat))))) ((17143990 : Rat)/10000000) .lt,
  -- E027.lower; E027: 17332529/10000000 < E_minus(11/20); E_plus(11/20) < 17332532/10000000.
  Comparison.ofRats ((17332529 : Rat)/10000000) ((expLower (((11 : Rat) / (20 : Rat))))) .lt,
  -- E027.upper; E027: 17332529/10000000 < E_minus(11/20); E_plus(11/20) < 17332532/10000000.
  Comparison.ofRats ((expUpper (((11 : Rat) / (20 : Rat))))) ((17332532 : Rat)/10000000) .lt,
  -- E028.lower; E028: 17346075/10000000 < E_minus(141/256); E_plus(141/256) < 17346078/10000000.
  Comparison.ofRats ((17346075 : Rat)/10000000) ((expLower (((141 : Rat) / (256 : Rat))))) .lt,
  -- E028.upper; E028: 17346075/10000000 < E_minus(141/256); E_plus(141/256) < 17346078/10000000.
  Comparison.ofRats ((expUpper (((141 : Rat) / (256 : Rat))))) ((17346078 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict008
