module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict021

def records : List Comparison := [
  -- E125.lower; E125: 51583923/10000000 < E_minus(105/64); E_plus(105/64) < 51583931/10000000.
  Comparison.ofRats ((51583923 : Rat)/10000000) ((expLower (((105 : Rat) / (64 : Rat))))) .lt,
  -- E125.upper; E125: 51583923/10000000 < E_minus(105/64); E_plus(105/64) < 51583931/10000000.
  Comparison.ofRats ((expUpper (((105 : Rat) / (64 : Rat))))) ((51583931 : Rat)/10000000) .lt,
  -- E126.lower; E126: 54059488/10000000 < E_minus(27/16); E_plus(27/16) < 54059496/10000000.
  Comparison.ofRats ((54059488 : Rat)/10000000) ((expLower (((27 : Rat) / (16 : Rat))))) .lt,
  -- E126.upper; E126: 54059488/10000000 < E_minus(27/16); E_plus(27/16) < 54059496/10000000.
  Comparison.ofRats ((expUpper (((27 : Rat) / (16 : Rat))))) ((54059496 : Rat)/10000000) .lt,
  -- E127.lower; E127: 56653857/10000000 < E_minus(111/64); E_plus(111/64) < 56653866/10000000.
  Comparison.ofRats ((56653857 : Rat)/10000000) ((expLower (((111 : Rat) / (64 : Rat))))) .lt,
  -- E127.upper; E127: 56653857/10000000 < E_minus(111/64); E_plus(111/64) < 56653866/10000000.
  Comparison.ofRats ((expUpper (((111 : Rat) / (64 : Rat))))) ((56653866 : Rat)/10000000) .lt,
  -- E128.lower; E128: 59372732/10000000 < E_minus(57/32); E_plus(57/32) < 59372743/10000000.
  Comparison.ofRats ((59372732 : Rat)/10000000) ((expLower (((57 : Rat) / (32 : Rat))))) .lt,
  -- E128.upper; E128: 59372732/10000000 < E_minus(57/32); E_plus(57/32) < 59372743/10000000.
  Comparison.ofRats ((expUpper (((57 : Rat) / (32 : Rat))))) ((59372743 : Rat)/10000000) .lt,
  -- E129.lower; E129: 62222089/10000000 < E_minus(117/64); E_plus(117/64) < 62222103/10000000.
  Comparison.ofRats ((62222089 : Rat)/10000000) ((expLower (((117 : Rat) / (64 : Rat))))) .lt,
  -- E129.upper; E129: 62222089/10000000 < E_minus(117/64); E_plus(117/64) < 62222103/10000000.
  Comparison.ofRats ((expUpper (((117 : Rat) / (64 : Rat))))) ((62222103 : Rat)/10000000) .lt,
  -- E130.lower; E130: 65208190/10000000 < E_minus(15/8); E_plus(15/8) < 65208206/10000000.
  Comparison.ofRats ((65208190 : Rat)/10000000) ((expLower (((15 : Rat) / (8 : Rat))))) .lt,
  -- E130.upper; E130: 65208190/10000000 < E_minus(15/8); E_plus(15/8) < 65208206/10000000.
  Comparison.ofRats ((expUpper (((15 : Rat) / (8 : Rat))))) ((65208206 : Rat)/10000000) .lt,
  -- E131.lower; E131: 68337596/10000000 < E_minus(123/64); E_plus(123/64) < 68337615/10000000.
  Comparison.ofRats ((68337596 : Rat)/10000000) ((expLower (((123 : Rat) / (64 : Rat))))) .lt,
  -- E131.upper; E131: 68337596/10000000 < E_minus(123/64); E_plus(123/64) < 68337615/10000000.
  Comparison.ofRats ((expUpper (((123 : Rat) / (64 : Rat))))) ((68337615 : Rat)/10000000) .lt,
  -- E132.lower; E132: 71617186/10000000 < E_minus(63/32); E_plus(63/32) < 71617209/10000000.
  Comparison.ofRats ((71617186 : Rat)/10000000) ((expLower (((63 : Rat) / (32 : Rat))))) .lt,
  -- E132.upper; E132: 71617186/10000000 < E_minus(63/32); E_plus(63/32) < 71617209/10000000.
  Comparison.ofRats ((expUpper (((63 : Rat) / (32 : Rat))))) ((71617209 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict021
