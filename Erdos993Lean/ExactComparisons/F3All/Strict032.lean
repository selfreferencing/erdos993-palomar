module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict032

def records : List Comparison := [
  -- P064.lower; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats ((6567486 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((376947 : Rat) / (312500 : Rat))))))) .lt,
  -- P064.upper; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))))) ((6567493 : Rat)/10000000) .lt,
  -- P065.lower; P065: lambda=28/25, y=9/32: 6127067/10000000 < L_minus(1+(28/25)/(13247849/10000000)); L_plus(1+(28/25)/(6623923/5000000)) < 6127074/10000000.
  Comparison.ofRats ((6127067 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))))) .lt,
  -- P065.upper; P065: lambda=28/25, y=9/32: 6127067/10000000 < L_minus(1+(28/25)/(13247849/10000000)); L_plus(1+(28/25)/(6623923/5000000)) < 6127074/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))))) ((6127074 : Rat)/10000000) .lt,
  -- P066.lower; P066: lambda=28/25, y=3/8: 5708459/10000000 < L_minus(1+(28/25)/(3637479/2500000)); L_plus(1+(28/25)/(14549913/10000000)) < 5708465/10000000.
  Comparison.ofRats ((5708459 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P066.upper; P066: lambda=28/25, y=3/8: 5708459/10000000 < L_minus(1+(28/25)/(3637479/2500000)); L_plus(1+(28/25)/(14549913/10000000)) < 5708465/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((5708465 : Rat)/10000000) .lt,
  -- P067.lower; P067: lambda=28/25, y=27/64: 5507269/10000000 < L_minus(1+(28/25)/(15248181/10000000)); L_plus(1+(28/25)/(7624089/5000000)) < 5507275/10000000.
  Comparison.ofRats ((5507269 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))))) .lt,
  -- P067.upper; P067: lambda=28/25, y=27/64: 5507269/10000000 < L_minus(1+(28/25)/(15248181/10000000)); L_plus(1+(28/25)/(7624089/5000000)) < 5507275/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))))) ((5507275 : Rat)/10000000) .lt,
  -- P068.lower; P068: lambda=28/25, y=15/32: 5311443/10000000 < L_minus(1+(28/25)/(3994989/2500000)); L_plus(1+(28/25)/(15979953/10000000)) < 5311449/10000000.
  Comparison.ofRats ((5311443 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))))) .lt,
  -- P068.upper; P068: lambda=28/25, y=15/32: 5311443/10000000 < L_minus(1+(28/25)/(3994989/2500000)); L_plus(1+(28/25)/(15979953/10000000)) < 5311449/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))))) ((5311449 : Rat)/10000000) .lt,
  -- P069.lower; P069: lambda=28/25, y=63/128: 5215529/10000000 < L_minus(1+(28/25)/(1635891/1000000)); L_plus(1+(28/25)/(16358907/10000000)) < 5215535/10000000.
  Comparison.ofRats ((5215529 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1635891 : Rat) / (1000000 : Rat))))))) .lt,
  -- P069.upper; P069: lambda=28/25, y=63/128: 5215529/10000000 < L_minus(1+(28/25)/(1635891/1000000)); L_plus(1+(28/25)/(16358907/10000000)) < 5215535/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((16358907 : Rat) / (10000000 : Rat))))))) ((5215535 : Rat)/10000000) .lt,
  -- P070.lower; P070: lambda=28/25, y=33/64: 5120941/10000000 < L_minus(1+(28/25)/(334937/200000)); L_plus(1+(28/25)/(16746847/10000000)) < 5120946/10000000.
  Comparison.ofRats ((5120941 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((334937 : Rat) / (200000 : Rat))))))) .lt,
  -- P070.upper; P070: lambda=28/25, y=33/64: 5120941/10000000 < L_minus(1+(28/25)/(334937/200000)); L_plus(1+(28/25)/(16746847/10000000)) < 5120946/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((16746847 : Rat) / (10000000 : Rat))))))) ((5120946 : Rat)/10000000) .lt,
  -- P071.lower; P071: lambda=28/25, y=69/128: 5027671/10000000 < L_minus(1+(28/25)/(1714399/1000000)); L_plus(1+(28/25)/(17143987/10000000)) < 5027677/10000000.
  Comparison.ofRats ((5027671 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1714399 : Rat) / (1000000 : Rat))))))) .lt,
  -- P071.upper; P071: lambda=28/25, y=69/128: 5027671/10000000 < L_minus(1+(28/25)/(1714399/1000000)); L_plus(1+(28/25)/(17143987/10000000)) < 5027677/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((17143987 : Rat) / (10000000 : Rat))))))) ((5027677 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict032
