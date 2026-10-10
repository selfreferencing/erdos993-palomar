module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict019

def records : List Comparison := [
  -- E109.lower; E109: 34631807/10000000 < E_minus(159/128); E_plus(159/128) < 34631811/10000000.
  Comparison.ofRats ((34631807 : Rat)/10000000) ((expLower (((159 : Rat) / (128 : Rat))))) .lt,
  -- E109.upper; E109: 34631807/10000000 < E_minus(159/128); E_plus(159/128) < 34631811/10000000.
  Comparison.ofRats ((expUpper (((159 : Rat) / (128 : Rat))))) ((34631811 : Rat)/10000000) .lt,
  -- E110.lower; E110: 35453077/10000000 < E_minus(81/64); E_plus(81/64) < 35453081/10000000.
  Comparison.ofRats ((35453077 : Rat)/10000000) ((expLower (((81 : Rat) / (64 : Rat))))) .lt,
  -- E110.upper; E110: 35453077/10000000 < E_minus(81/64); E_plus(81/64) < 35453081/10000000.
  Comparison.ofRats ((expUpper (((81 : Rat) / (64 : Rat))))) ((35453081 : Rat)/10000000) .lt,
  -- E111.lower; E111: 36293823/10000000 < E_minus(165/128); E_plus(165/128) < 36293826/10000000.
  Comparison.ofRats ((36293823 : Rat)/10000000) ((expLower (((165 : Rat) / (128 : Rat))))) .lt,
  -- E111.upper; E111: 36293823/10000000 < E_minus(165/128); E_plus(165/128) < 36293826/10000000.
  Comparison.ofRats ((expUpper (((165 : Rat) / (128 : Rat))))) ((36293826 : Rat)/10000000) .lt,
  -- E112.lower; E112: 37154506/10000000 < E_minus(21/16); E_plus(21/16) < 37154509/10000000.
  Comparison.ofRats ((37154506 : Rat)/10000000) ((expLower (((21 : Rat) / (16 : Rat))))) .lt,
  -- E112.upper; E112: 37154506/10000000 < E_minus(21/16); E_plus(21/16) < 37154509/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (16 : Rat))))) ((37154509 : Rat)/10000000) .lt,
  -- E113.lower; E113: 38035600/10000000 < E_minus(171/128); E_plus(171/128) < 38035603/10000000.
  Comparison.ofRats ((38035600 : Rat)/10000000) ((expLower (((171 : Rat) / (128 : Rat))))) .lt,
  -- E113.upper; E113: 38035600/10000000 < E_minus(171/128); E_plus(171/128) < 38035603/10000000.
  Comparison.ofRats ((expUpper (((171 : Rat) / (128 : Rat))))) ((38035603 : Rat)/10000000) .lt,
  -- E114.lower; E114: 38937588/10000000 < E_minus(87/64); E_plus(87/64) < 38937592/10000000.
  Comparison.ofRats ((38937588 : Rat)/10000000) ((expLower (((87 : Rat) / (64 : Rat))))) .lt,
  -- E114.upper; E114: 38937588/10000000 < E_minus(87/64); E_plus(87/64) < 38937592/10000000.
  Comparison.ofRats ((expUpper (((87 : Rat) / (64 : Rat))))) ((38937592 : Rat)/10000000) .lt,
  -- E115.lower; E115: 39860966/10000000 < E_minus(177/128); E_plus(177/128) < 39860970/10000000.
  Comparison.ofRats ((39860966 : Rat)/10000000) ((expLower (((177 : Rat) / (128 : Rat))))) .lt,
  -- E115.upper; E115: 39860966/10000000 < E_minus(177/128); E_plus(177/128) < 39860970/10000000.
  Comparison.ofRats ((expUpper (((177 : Rat) / (128 : Rat))))) ((39860970 : Rat)/10000000) .lt,
  -- E116.lower; E116: 40806242/10000000 < E_minus(45/32); E_plus(45/32) < 40806246/10000000.
  Comparison.ofRats ((40806242 : Rat)/10000000) ((expLower (((45 : Rat) / (32 : Rat))))) .lt,
  -- E116.upper; E116: 40806242/10000000 < E_minus(45/32); E_plus(45/32) < 40806246/10000000.
  Comparison.ofRats ((expUpper (((45 : Rat) / (32 : Rat))))) ((40806246 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict019
