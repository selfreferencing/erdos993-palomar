module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict007

def records : List Comparison := [
  -- E013.lower; E013: 14549913/10000000 < E_minus(3/8); E_plus(3/8) < 14549916/10000000.
  Comparison.ofRats ((14549913 : Rat)/10000000) ((expLower (((3 : Rat) / (8 : Rat))))) .lt,
  -- E013.upper; E013: 14549913/10000000 < E_minus(3/8); E_plus(3/8) < 14549916/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (8 : Rat))))) ((14549916 : Rat)/10000000) .lt,
  -- E014.lower; E014: 14894954/10000000 < E_minus(51/128); E_plus(51/128) < 14894957/10000000.
  Comparison.ofRats ((14894954 : Rat)/10000000) ((expLower (((51 : Rat) / (128 : Rat))))) .lt,
  -- E014.upper; E014: 14894954/10000000 < E_minus(51/128); E_plus(51/128) < 14894957/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (128 : Rat))))) ((14894957 : Rat)/10000000) .lt,
  -- E015.lower; E015: 15219614/10000000 < E_minus(21/50); E_plus(21/50) < 15219617/10000000.
  Comparison.ofRats ((15219614 : Rat)/10000000) ((expLower (((21 : Rat) / (50 : Rat))))) .lt,
  -- E015.upper; E015: 15219614/10000000 < E_minus(21/50); E_plus(21/50) < 15219617/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (50 : Rat))))) ((15219617 : Rat)/10000000) .lt,
  -- E016.lower; E016: 15248178/10000000 < E_minus(27/64); E_plus(27/64) < 15248181/10000000.
  Comparison.ofRats ((15248178 : Rat)/10000000) ((expLower (((27 : Rat) / (64 : Rat))))) .lt,
  -- E016.upper; E016: 15248178/10000000 < E_minus(27/64); E_plus(27/64) < 15248181/10000000.
  Comparison.ofRats ((expUpper (((27 : Rat) / (64 : Rat))))) ((15248181 : Rat)/10000000) .lt,
  -- E017.lower; E017: 15609778/10000000 < E_minus(57/128); E_plus(57/128) < 15609781/10000000.
  Comparison.ofRats ((15609778 : Rat)/10000000) ((expLower (((57 : Rat) / (128 : Rat))))) .lt,
  -- E017.upper; E017: 15609778/10000000 < E_minus(57/128); E_plus(57/128) < 15609781/10000000.
  Comparison.ofRats ((expUpper (((57 : Rat) / (128 : Rat))))) ((15609781 : Rat)/10000000) .lt,
  -- E018.lower; E018: 15840738/10000000 < E_minus(23/50); E_plus(23/50) < 15840741/10000000.
  Comparison.ofRats ((15840738 : Rat)/10000000) ((expLower (((23 : Rat) / (50 : Rat))))) .lt,
  -- E018.upper; E018: 15840738/10000000 < E_minus(23/50); E_plus(23/50) < 15840741/10000000.
  Comparison.ofRats ((expUpper (((23 : Rat) / (50 : Rat))))) ((15840741 : Rat)/10000000) .lt,
  -- E019.lower; E019: 15979953/10000000 < E_minus(15/32); E_plus(15/32) < 15979956/10000000.
  Comparison.ofRats ((15979953 : Rat)/10000000) ((expLower (((15 : Rat) / (32 : Rat))))) .lt,
  -- E019.upper; E019: 15979953/10000000 < E_minus(15/32); E_plus(15/32) < 15979956/10000000.
  Comparison.ofRats ((expUpper (((15 : Rat) / (32 : Rat))))) ((15979956 : Rat)/10000000) .lt,
  -- E020.lower; E020: 16168320/10000000 < E_minus(123/256); E_plus(123/256) < 16168323/10000000.
  Comparison.ofRats ((16168320 : Rat)/10000000) ((expLower (((123 : Rat) / (256 : Rat))))) .lt,
  -- E020.upper; E020: 16168320/10000000 < E_minus(123/256); E_plus(123/256) < 16168323/10000000.
  Comparison.ofRats ((expUpper (((123 : Rat) / (256 : Rat))))) ((16168323 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict007
