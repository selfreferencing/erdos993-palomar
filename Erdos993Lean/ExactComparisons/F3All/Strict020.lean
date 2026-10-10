module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict020

def records : List Comparison := [
  -- E117.lower; E117: 41773934/10000000 < E_minus(183/128); E_plus(183/128) < 41773938/10000000.
  Comparison.ofRats ((41773934 : Rat)/10000000) ((expLower (((183 : Rat) / (128 : Rat))))) .lt,
  -- E117.upper; E117: 41773934/10000000 < E_minus(183/128); E_plus(183/128) < 41773938/10000000.
  Comparison.ofRats ((expUpper (((183 : Rat) / (128 : Rat))))) ((41773938 : Rat)/10000000) .lt,
  -- E118.lower; E118: 42764574/10000000 < E_minus(93/64); E_plus(93/64) < 42764579/10000000.
  Comparison.ofRats ((42764574 : Rat)/10000000) ((expLower (((93 : Rat) / (64 : Rat))))) .lt,
  -- E118.upper; E118: 42764574/10000000 < E_minus(93/64); E_plus(93/64) < 42764579/10000000.
  Comparison.ofRats ((expUpper (((93 : Rat) / (64 : Rat))))) ((42764579 : Rat)/10000000) .lt,
  -- E119.lower; E119: 43778707/10000000 < E_minus(189/128); E_plus(189/128) < 43778712/10000000.
  Comparison.ofRats ((43778707 : Rat)/10000000) ((expLower (((189 : Rat) / (128 : Rat))))) .lt,
  -- E119.upper; E119: 43778707/10000000 < E_minus(189/128); E_plus(189/128) < 43778712/10000000.
  Comparison.ofRats ((expUpper (((189 : Rat) / (128 : Rat))))) ((43778712 : Rat)/10000000) .lt,
  -- E120.lower; E120: 44816889/10000000 < E_minus(3/2); E_plus(3/2) < 44816894/10000000.
  Comparison.ofRats ((44816889 : Rat)/10000000) ((expLower (((3 : Rat) / (2 : Rat))))) .lt,
  -- E120.upper; E120: 44816889/10000000 < E_minus(3/2); E_plus(3/2) < 44816894/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (2 : Rat))))) ((44816894 : Rat)/10000000) .lt,
  -- E121.lower; E121: 45879691/10000000 < E_minus(195/128); E_plus(195/128) < 45879696/10000000.
  Comparison.ofRats ((45879691 : Rat)/10000000) ((expLower (((195 : Rat) / (128 : Rat))))) .lt,
  -- E121.upper; E121: 45879691/10000000 < E_minus(195/128); E_plus(195/128) < 45879696/10000000.
  Comparison.ofRats ((expUpper (((195 : Rat) / (128 : Rat))))) ((45879696 : Rat)/10000000) .lt,
  -- E122.lower; E122: 46967697/10000000 < E_minus(99/64); E_plus(99/64) < 46967702/10000000.
  Comparison.ofRats ((46967697 : Rat)/10000000) ((expLower (((99 : Rat) / (64 : Rat))))) .lt,
  -- E122.upper; E122: 46967697/10000000 < E_minus(99/64); E_plus(99/64) < 46967702/10000000.
  Comparison.ofRats ((expUpper (((99 : Rat) / (64 : Rat))))) ((46967702 : Rat)/10000000) .lt,
  -- E123.lower; E123: 48081504/10000000 < E_minus(201/128); E_plus(201/128) < 48081509/10000000.
  Comparison.ofRats ((48081504 : Rat)/10000000) ((expLower (((201 : Rat) / (128 : Rat))))) .lt,
  -- E123.upper; E123: 48081504/10000000 < E_minus(201/128); E_plus(201/128) < 48081509/10000000.
  Comparison.ofRats ((expUpper (((201 : Rat) / (128 : Rat))))) ((48081509 : Rat)/10000000) .lt,
  -- E124.lower; E124: 49221724/10000000 < E_minus(51/32); E_plus(51/32) < 49221730/10000000.
  Comparison.ofRats ((49221724 : Rat)/10000000) ((expLower (((51 : Rat) / (32 : Rat))))) .lt,
  -- E124.upper; E124: 49221724/10000000 < E_minus(51/32); E_plus(51/32) < 49221730/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (32 : Rat))))) ((49221730 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict020
