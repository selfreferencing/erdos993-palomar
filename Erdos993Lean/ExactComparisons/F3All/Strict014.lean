module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict014

def records : List Comparison := [
  -- E069.lower; E069: 22979816/10000000 < E_minus(213/256); E_plus(213/256) < 22979819/10000000.
  Comparison.ofRats ((22979816 : Rat)/10000000) ((expLower (((213 : Rat) / (256 : Rat))))) .lt,
  -- E069.upper; E069: 22979816/10000000 < E_minus(213/256); E_plus(213/256) < 22979819/10000000.
  Comparison.ofRats ((expUpper (((213 : Rat) / (256 : Rat))))) ((22979819 : Rat)/10000000) .lt,
  -- E070.lower; E070: 23163668/10000000 < E_minus(21/25); E_plus(21/25) < 23163671/10000000.
  Comparison.ofRats ((23163668 : Rat)/10000000) ((expLower (((21 : Rat) / (25 : Rat))))) .lt,
  -- E070.upper; E070: 23163668/10000000 < E_minus(21/25); E_plus(21/25) < 23163671/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (25 : Rat))))) ((23163671 : Rat)/10000000) .lt,
  -- E071.lower; E071: 23250695/10000000 < E_minus(27/32); E_plus(27/32) < 23250698/10000000.
  Comparison.ofRats ((23250695 : Rat)/10000000) ((expLower (((27 : Rat) / (32 : Rat))))) .lt,
  -- E071.upper; E071: 23250695/10000000 < E_minus(27/32); E_plus(27/32) < 23250698/10000000.
  Comparison.ofRats ((expUpper (((27 : Rat) / (32 : Rat))))) ((23250698 : Rat)/10000000) .lt,
  -- E072.lower; E072: 23414753/10000000 < E_minus(1089/1280); E_plus(1089/1280) < 23414756/10000000.
  Comparison.ofRats ((23414753 : Rat)/10000000) ((expLower (((1089 : Rat) / (1280 : Rat))))) .lt,
  -- E072.upper; E072: 23414753/10000000 < E_minus(1089/1280); E_plus(1089/1280) < 23414756/10000000.
  Comparison.ofRats ((expUpper (((1089 : Rat) / (1280 : Rat))))) ((23414756 : Rat)/10000000) .lt,
  -- E073.lower; E073: 23524767/10000000 < E_minus(219/256); E_plus(219/256) < 23524770/10000000.
  Comparison.ofRats ((23524767 : Rat)/10000000) ((expLower (((219 : Rat) / (256 : Rat))))) .lt,
  -- E073.upper; E073: 23524767/10000000 < E_minus(219/256); E_plus(219/256) < 23524770/10000000.
  Comparison.ofRats ((expUpper (((219 : Rat) / (256 : Rat))))) ((23524770 : Rat)/10000000) .lt,
  -- E074.lower; E074: 23616840/10000000 < E_minus(55/64); E_plus(55/64) < 23616843/10000000.
  Comparison.ofRats ((23616840 : Rat)/10000000) ((expLower (((55 : Rat) / (64 : Rat))))) .lt,
  -- E074.upper; E074: 23616840/10000000 < E_minus(55/64); E_plus(55/64) < 23616843/10000000.
  Comparison.ofRats ((expUpper (((55 : Rat) / (64 : Rat))))) ((23616843 : Rat)/10000000) .lt,
  -- E075.lower; E075: 23637145/10000000 < E_minus(11011/12800); E_plus(11011/12800) < 23637148/10000000.
  Comparison.ofRats ((23637145 : Rat)/10000000) ((expLower (((11011 : Rat) / (12800 : Rat))))) .lt,
  -- E075.upper; E075: 23637145/10000000 < E_minus(11011/12800); E_plus(11011/12800) < 23637148/10000000.
  Comparison.ofRats ((expUpper (((11011 : Rat) / (12800 : Rat))))) ((23637148 : Rat)/10000000) .lt,
  -- E076.lower; E076: 23802069/10000000 < E_minus(111/128); E_plus(111/128) < 23802073/10000000.
  Comparison.ofRats ((23802069 : Rat)/10000000) ((expLower (((111 : Rat) / (128 : Rat))))) .lt,
  -- E076.upper; E076: 23802069/10000000 < E_minus(111/128); E_plus(111/128) < 23802073/10000000.
  Comparison.ofRats ((expUpper (((111 : Rat) / (128 : Rat))))) ((23802073 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict014
