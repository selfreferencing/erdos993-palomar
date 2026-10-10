module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict035

def records : List Comparison := [
  -- P088.lower; P088: lambda=28/25, y=63/64: 3496091/10000000 < L_minus(1+(28/25)/(26761389/10000000)); L_plus(1+(28/25)/(13380693/5000000)) < 3496097/10000000.
  Comparison.ofRats ((3496091 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((26761389 : Rat) / (10000000 : Rat))))))) .lt,
  -- P088.upper; P088: lambda=28/25, y=63/64: 3496091/10000000 < L_minus(1+(28/25)/(26761389/10000000)); L_plus(1+(28/25)/(13380693/5000000)) < 3496097/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((13380693 : Rat) / (5000000 : Rat))))))) ((3496097 : Rat)/10000000) .lt,
  -- P089.lower; P089: lambda=28/25, y=33/32: 3360063/10000000 < L_minus(1+(28/25)/(5609139/2000000)); L_plus(1+(28/25)/(7011423/2500000)) < 3360068/10000000.
  Comparison.ofRats ((3360063 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((5609139 : Rat) / (2000000 : Rat))))))) .lt,
  -- P089.upper; P089: lambda=28/25, y=33/32: 3360063/10000000 < L_minus(1+(28/25)/(5609139/2000000)); L_plus(1+(28/25)/(7011423/2500000)) < 3360068/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((7011423 : Rat) / (2500000 : Rat))))))) ((3360068 : Rat)/10000000) .lt,
  -- P090.lower; P090: lambda=28/25, y=69/64: 3228516/10000000 < L_minus(1+(28/25)/(7347909/2500000)); L_plus(1+(28/25)/(29391633/10000000)) < 3228521/10000000.
  Comparison.ofRats ((3228516 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((7347909 : Rat) / (2500000 : Rat))))))) .lt,
  -- P090.upper; P090: lambda=28/25, y=69/64: 3228516/10000000 < L_minus(1+(28/25)/(7347909/2500000)); L_plus(1+(28/25)/(29391633/10000000)) < 3228521/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((29391633 : Rat) / (10000000 : Rat))))))) ((3228521 : Rat)/10000000) .lt,
  -- P091.lower; P091: lambda=28/25, y=9/8: 3101358/10000000 < L_minus(1+(28/25)/(3080217/1000000)); L_plus(1+(28/25)/(30802167/10000000)) < 3101364/10000000.
  Comparison.ofRats ((3101358 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P091.upper; P091: lambda=28/25, y=9/8: 3101358/10000000 < L_minus(1+(28/25)/(3080217/1000000)); L_plus(1+(28/25)/(30802167/10000000)) < 3101364/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((3101364 : Rat)/10000000) .lt,
  -- P092.lower; P092: lambda=28/25, y=75/64: 2978497/10000000 < L_minus(1+(28/25)/(32280397/10000000)); L_plus(1+(28/25)/(16140197/5000000)) < 2978503/10000000.
  Comparison.ofRats ((2978497 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((32280397 : Rat) / (10000000 : Rat))))))) .lt,
  -- P092.upper; P092: lambda=28/25, y=75/64: 2978497/10000000 < L_minus(1+(28/25)/(32280397/10000000)); L_plus(1+(28/25)/(16140197/5000000)) < 2978503/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((16140197 : Rat) / (5000000 : Rat))))))) ((2978503 : Rat)/10000000) .lt,
  -- P093.lower; P093: lambda=28/25, y=39/32: 2859838/10000000 < L_minus(1+(28/25)/(16914783/5000000)); L_plus(1+(28/25)/(16914781/5000000)) < 2859844/10000000.
  Comparison.ofRats ((2859838 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((16914783 : Rat) / (5000000 : Rat))))))) .lt,
  -- P093.upper; P093: lambda=28/25, y=39/32: 2859838/10000000 < L_minus(1+(28/25)/(16914783/5000000)); L_plus(1+(28/25)/(16914781/5000000)) < 2859844/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((16914781 : Rat) / (5000000 : Rat))))))) ((2859844 : Rat)/10000000) .lt,
  -- P094.lower; P094: lambda=28/25, y=81/64: 2745285/10000000 < L_minus(1+(28/25)/(35453081/10000000)); L_plus(1+(28/25)/(35453077/10000000)) < 2745290/10000000.
  Comparison.ofRats ((2745285 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((35453081 : Rat) / (10000000 : Rat))))))) .lt,
  -- P094.upper; P094: lambda=28/25, y=81/64: 2745285/10000000 < L_minus(1+(28/25)/(35453081/10000000)); L_plus(1+(28/25)/(35453077/10000000)) < 2745290/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((35453077 : Rat) / (10000000 : Rat))))))) ((2745290 : Rat)/10000000) .lt,
  -- P095.lower; P095: lambda=28/25, y=21/16: 2634740/10000000 < L_minus(1+(28/25)/(37154509/10000000)); L_plus(1+(28/25)/(18577253/5000000)) < 2634746/10000000.
  Comparison.ofRats ((2634740 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P095.upper; P095: lambda=28/25, y=21/16: 2634740/10000000 < L_minus(1+(28/25)/(37154509/10000000)); L_plus(1+(28/25)/(18577253/5000000)) < 2634746/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((2634746 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict035
