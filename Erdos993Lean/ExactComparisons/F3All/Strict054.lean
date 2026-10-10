module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict054

def records : List Comparison := [
  -- P240.lower; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats ((6100912 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((693949 : Rat) / (250000 : Rat))))))) .lt,
  -- P240.upper; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((27757957 : Rat) / (10000000 : Rat))))))) ((6100917 : Rat)/10000000) .lt,
  -- P241.lower; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats ((5929994 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((14413827 : Rat) / (5000000 : Rat))))))) .lt,
  -- P241.upper; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((28827651 : Rat) / (10000000 : Rat))))))) ((5930000 : Rat)/10000000) .lt,
  -- P242.lower; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats ((5639048 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P242.upper; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((5639054 : Rat)/10000000) .lt,
  -- P243.lower; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats ((5281506 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((261991 : Rat) / (78125 : Rat))))))) .lt,
  -- P243.upper; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6706969 : Rat) / (2000000 : Rat))))))) ((5281511 : Rat)/10000000) .lt,
  -- P244.lower; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats ((4873570 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P244.upper; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((4873575 : Rat)/10000000) .lt,
  -- P245.lower; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats ((4191291 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P245.upper; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((4191296 : Rat)/10000000) .lt,
  -- P246.lower; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats ((3588086 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P246.upper; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((3588092 : Rat)/10000000) .lt,
  -- P247.lower; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats ((3058862 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((32604103 : Rat) / (5000000 : Rat))))))) .lt,
  -- P247.upper; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6520819 : Rat) / (1000000 : Rat))))))) ((3058868 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict054
