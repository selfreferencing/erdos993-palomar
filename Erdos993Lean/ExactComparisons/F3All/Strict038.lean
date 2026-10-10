module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict038

def records : List Comparison := [
  -- P112.lower; P112: lambda=263/200, y=27/64: 6218646/10000000 < L_minus(1+(263/200)/(15248181/10000000)); L_plus(1+(263/200)/(7624089/5000000)) < 6218652/10000000.
  Comparison.ofRats ((6218646 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))))) .lt,
  -- P112.upper; P112: lambda=263/200, y=27/64: 6218646/10000000 < L_minus(1+(263/200)/(15248181/10000000)); L_plus(1+(263/200)/(7624089/5000000)) < 6218652/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))))) ((6218652 : Rat)/10000000) .lt,
  -- P113.lower; P113: lambda=263/200, y=15/32: 6004316/10000000 < L_minus(1+(263/200)/(3994989/2500000)); L_plus(1+(263/200)/(15979953/10000000)) < 6004322/10000000.
  Comparison.ofRats ((6004316 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))))) .lt,
  -- P113.upper; P113: lambda=263/200, y=15/32: 6004316/10000000 < L_minus(1+(263/200)/(3994989/2500000)); L_plus(1+(263/200)/(15979953/10000000)) < 6004322/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))))) ((6004322 : Rat)/10000000) .lt,
  -- P114.lower; P114: lambda=263/200, y=63/128: 5899193/10000000 < L_minus(1+(263/200)/(1635891/1000000)); L_plus(1+(263/200)/(16358907/10000000)) < 5899199/10000000.
  Comparison.ofRats ((5899193 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1635891 : Rat) / (1000000 : Rat))))))) .lt,
  -- P114.upper; P114: lambda=263/200, y=63/128: 5899193/10000000 < L_minus(1+(263/200)/(1635891/1000000)); L_plus(1+(263/200)/(16358907/10000000)) < 5899199/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16358907 : Rat) / (10000000 : Rat))))))) ((5899199 : Rat)/10000000) .lt,
  -- P115.lower; P115: lambda=263/200, y=33/64: 5795427/10000000 < L_minus(1+(263/200)/(334937/200000)); L_plus(1+(263/200)/(16746847/10000000)) < 5795433/10000000.
  Comparison.ofRats ((5795427 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((334937 : Rat) / (200000 : Rat))))))) .lt,
  -- P115.upper; P115: lambda=263/200, y=33/64: 5795427/10000000 < L_minus(1+(263/200)/(334937/200000)); L_plus(1+(263/200)/(16746847/10000000)) < 5795433/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16746847 : Rat) / (10000000 : Rat))))))) ((5795433 : Rat)/10000000) .lt,
  -- P116.lower; P116: lambda=263/200, y=69/128: 5693014/10000000 < L_minus(1+(263/200)/(1714399/1000000)); L_plus(1+(263/200)/(17143987/10000000)) < 5693020/10000000.
  Comparison.ofRats ((5693014 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1714399 : Rat) / (1000000 : Rat))))))) .lt,
  -- P116.upper; P116: lambda=263/200, y=69/128: 5693014/10000000 < L_minus(1+(263/200)/(1714399/1000000)); L_plus(1+(263/200)/(17143987/10000000)) < 5693020/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((17143987 : Rat) / (10000000 : Rat))))))) ((5693020 : Rat)/10000000) .lt,
  -- P117.lower; P117: lambda=263/200, y=9/16: 5591951/10000000 < L_minus(1+(263/200)/(4387637/2500000)); L_plus(1+(263/200)/(3510109/2000000)) < 5591956/10000000.
  Comparison.ofRats ((5591951 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P117.upper; P117: lambda=263/200, y=9/16: 5591951/10000000 < L_minus(1+(263/200)/(4387637/2500000)); L_plus(1+(263/200)/(3510109/2000000)) < 5591956/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((5591956 : Rat)/10000000) .lt,
  -- P118.lower; P118: lambda=263/200, y=75/128: 5492232/10000000 < L_minus(1+(263/200)/(17966747/10000000)); L_plus(1+(263/200)/(2245843/1250000)) < 5492238/10000000.
  Comparison.ofRats ((5492232 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((17966747 : Rat) / (10000000 : Rat))))))) .lt,
  -- P118.upper; P118: lambda=263/200, y=75/128: 5492232/10000000 < L_minus(1+(263/200)/(17966747/10000000)); L_plus(1+(263/200)/(2245843/1250000)) < 5492238/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((2245843 : Rat) / (1250000 : Rat))))))) ((5492238 : Rat)/10000000) .lt,
  -- P119.lower; P119: lambda=263/200, y=39/64: 5393854/10000000 < L_minus(1+(263/200)/(1149551/625000)); L_plus(1+(263/200)/(18392813/10000000)) < 5393860/10000000.
  Comparison.ofRats ((5393854 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((1149551 : Rat) / (625000 : Rat))))))) .lt,
  -- P119.upper; P119: lambda=263/200, y=39/64: 5393854/10000000 < L_minus(1+(263/200)/(1149551/625000)); L_plus(1+(263/200)/(18392813/10000000)) < 5393860/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18392813 : Rat) / (10000000 : Rat))))))) ((5393860 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict038
