module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict009

def records : List Comparison := [
  -- E029.lower; E029: 17550545/10000000 < E_minus(9/16); E_plus(9/16) < 17550548/10000000.
  Comparison.ofRats ((17550545 : Rat)/10000000) ((expLower (((9 : Rat) / (16 : Rat))))) .lt,
  -- E029.upper; E029: 17550545/10000000 < E_minus(9/16); E_plus(9/16) < 17550548/10000000.
  Comparison.ofRats ((expUpper (((9 : Rat) / (16 : Rat))))) ((17550548 : Rat)/10000000) .lt,
  -- E030.lower; E030: 17757425/10000000 < E_minus(147/256); E_plus(147/256) < 17757428/10000000.
  Comparison.ofRats ((17757425 : Rat)/10000000) ((expLower (((147 : Rat) / (256 : Rat))))) .lt,
  -- E030.upper; E030: 17757425/10000000 < E_minus(147/256); E_plus(147/256) < 17757428/10000000.
  Comparison.ofRats ((expUpper (((147 : Rat) / (256 : Rat))))) ((17757428 : Rat)/10000000) .lt,
  -- E031.lower; E031: 17966744/10000000 < E_minus(75/128); E_plus(75/128) < 17966747/10000000.
  Comparison.ofRats ((17966744 : Rat)/10000000) ((expLower (((75 : Rat) / (128 : Rat))))) .lt,
  -- E031.upper; E031: 17966744/10000000 < E_minus(75/128); E_plus(75/128) < 17966747/10000000.
  Comparison.ofRats ((expUpper (((75 : Rat) / (128 : Rat))))) ((17966747 : Rat)/10000000) .lt,
  -- E032.lower; E032: 18178531/10000000 < E_minus(153/256); E_plus(153/256) < 18178534/10000000.
  Comparison.ofRats ((18178531 : Rat)/10000000) ((expLower (((153 : Rat) / (256 : Rat))))) .lt,
  -- E032.upper; E032: 18178531/10000000 < E_minus(153/256); E_plus(153/256) < 18178534/10000000.
  Comparison.ofRats ((expUpper (((153 : Rat) / (256 : Rat))))) ((18178534 : Rat)/10000000) .lt,
  -- E033.lower; E033: 18312521/10000000 < E_minus(121/200); E_plus(121/200) < 18312524/10000000.
  Comparison.ofRats ((18312521 : Rat)/10000000) ((expLower (((121 : Rat) / (200 : Rat))))) .lt,
  -- E033.upper; E033: 18312521/10000000 < E_minus(121/200); E_plus(121/200) < 18312524/10000000.
  Comparison.ofRats ((expUpper (((121 : Rat) / (200 : Rat))))) ((18312524 : Rat)/10000000) .lt,
  -- E034.lower; E034: 18392813/10000000 < E_minus(39/64); E_plus(39/64) < 18392816/10000000.
  Comparison.ofRats ((18392813 : Rat)/10000000) ((expLower (((39 : Rat) / (64 : Rat))))) .lt,
  -- E034.upper; E034: 18392813/10000000 < E_minus(39/64); E_plus(39/64) < 18392816/10000000.
  Comparison.ofRats ((expUpper (((39 : Rat) / (64 : Rat))))) ((18392816 : Rat)/10000000) .lt,
  -- E035.lower; E035: 18609622/10000000 < E_minus(159/256); E_plus(159/256) < 18609625/10000000.
  Comparison.ofRats ((18609622 : Rat)/10000000) ((expLower (((159 : Rat) / (256 : Rat))))) .lt,
  -- E035.upper; E035: 18609622/10000000 < E_minus(159/256); E_plus(159/256) < 18609625/10000000.
  Comparison.ofRats ((expUpper (((159 : Rat) / (256 : Rat))))) ((18609625 : Rat)/10000000) .lt,
  -- E036.lower; E036: 18776104/10000000 < E_minus(63/100); E_plus(63/100) < 18776107/10000000.
  Comparison.ofRats ((18776104 : Rat)/10000000) ((expLower (((63 : Rat) / (100 : Rat))))) .lt,
  -- E036.upper; E036: 18776104/10000000 < E_minus(63/100); E_plus(63/100) < 18776107/10000000.
  Comparison.ofRats ((expUpper (((63 : Rat) / (100 : Rat))))) ((18776107 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict009
