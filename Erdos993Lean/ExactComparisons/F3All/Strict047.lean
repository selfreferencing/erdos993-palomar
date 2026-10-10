module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict047

def records : List Comparison := [
  -- P184.lower; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats ((7182621 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((16652913 : Rat) / (10000000 : Rat))))))) .lt,
  -- P184.upper; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((1665291 : Rat) / (1000000 : Rat))))))) ((7182630 : Rat)/10000000) .lt,
  -- P185.lower; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats ((6917055 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P185.upper; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((6917064 : Rat)/10000000) .lt,
  -- P186.lower; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats ((6549627 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((18917457 : Rat) / (10000000 : Rat))))))) .lt,
  -- P186.upper; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((9458727 : Rat) / (5000000 : Rat))))))) ((6549634 : Rat)/10000000) .lt,
  -- P187.lower; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats ((6024787 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P187.upper; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((6024793 : Rat)/10000000) .lt,
  -- P188.lower; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats ((5957184 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((4297989 : Rat) / (2000000 : Rat))))))) .lt,
  -- P188.upper; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((10744971 : Rat) / (5000000 : Rat))))))) ((5957189 : Rat)/10000000) .lt,
  -- P189.lower; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats ((5676067 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((1145227 : Rat) / (500000 : Rat))))))) .lt,
  -- P189.upper; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((22904537 : Rat) / (10000000 : Rat))))))) ((5676073 : Rat)/10000000) .lt,
  -- P190.lower; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats ((5404928 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((6103063 : Rat) / (2500000 : Rat))))))) .lt,
  -- P190.upper; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((24412249 : Rat) / (10000000 : Rat))))))) ((5404934 : Rat)/10000000) .lt,
  -- P191.lower; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats ((5219492 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P191.upper; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((5219497 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict047
