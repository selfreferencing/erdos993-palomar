module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict041

def records : List Comparison := [
  -- P136.lower; P136: lambda=263/200, y=57/64: 4315710/10000000 < L_minus(1+(263/200)/(12183261/5000000)); L_plus(1+(263/200)/(24366519/10000000)) < 4315716/10000000.
  Comparison.ofRats ((4315710 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((12183261 : Rat) / (5000000 : Rat))))))) .lt,
  -- P136.upper; P136: lambda=263/200, y=57/64: 4315710/10000000 < L_minus(1+(263/200)/(12183261/5000000)); L_plus(1+(263/200)/(24366519/10000000)) < 4315716/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((24366519 : Rat) / (10000000 : Rat))))))) ((4315716 : Rat)/10000000) .lt,
  -- P137.lower; P137: lambda=263/200, y=15/16: 4153897/10000000 < L_minus(1+(263/200)/(3191987/1250000)); L_plus(1+(263/200)/(25535893/10000000)) < 4153902/10000000.
  Comparison.ofRats ((4153897 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3191987 : Rat) / (1250000 : Rat))))))) .lt,
  -- P137.upper; P137: lambda=263/200, y=15/16: 4153897/10000000 < L_minus(1+(263/200)/(3191987/1250000)); L_plus(1+(263/200)/(25535893/10000000)) < 4153902/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((25535893 : Rat) / (10000000 : Rat))))))) ((4153902 : Rat)/10000000) .lt,
  -- P138.lower; P138: lambda=263/200, y=63/64: 3997013/10000000 < L_minus(1+(263/200)/(26761389/10000000)); L_plus(1+(263/200)/(13380693/5000000)) < 3997018/10000000.
  Comparison.ofRats ((3997013 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((26761389 : Rat) / (10000000 : Rat))))))) .lt,
  -- P138.upper; P138: lambda=263/200, y=63/64: 3997013/10000000 < L_minus(1+(263/200)/(26761389/10000000)); L_plus(1+(263/200)/(13380693/5000000)) < 3997018/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((13380693 : Rat) / (5000000 : Rat))))))) ((3997018 : Rat)/10000000) .lt,
  -- P139.lower; P139: lambda=263/200, y=33/32: 3844983/10000000 < L_minus(1+(263/200)/(5609139/2000000)); L_plus(1+(263/200)/(7011423/2500000)) < 3844988/10000000.
  Comparison.ofRats ((3844983 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((5609139 : Rat) / (2000000 : Rat))))))) .lt,
  -- P139.upper; P139: lambda=263/200, y=33/32: 3844983/10000000 < L_minus(1+(263/200)/(5609139/2000000)); L_plus(1+(263/200)/(7011423/2500000)) < 3844988/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7011423 : Rat) / (2500000 : Rat))))))) ((3844988 : Rat)/10000000) .lt,
  -- P140.lower; P140: lambda=263/200, y=69/64: 3697728/10000000 < L_minus(1+(263/200)/(7347909/2500000)); L_plus(1+(263/200)/(29391633/10000000)) < 3697734/10000000.
  Comparison.ofRats ((3697728 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((7347909 : Rat) / (2500000 : Rat))))))) .lt,
  -- P140.upper; P140: lambda=263/200, y=69/64: 3697728/10000000 < L_minus(1+(263/200)/(7347909/2500000)); L_plus(1+(263/200)/(29391633/10000000)) < 3697734/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((29391633 : Rat) / (10000000 : Rat))))))) ((3697734 : Rat)/10000000) .lt,
  -- P141.lower; P141: lambda=263/200, y=9/8: 3555166/10000000 < L_minus(1+(263/200)/(3080217/1000000)); L_plus(1+(263/200)/(30802167/10000000)) < 3555171/10000000.
  Comparison.ofRats ((3555166 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((3080217 : Rat) / (1000000 : Rat))))))) .lt,
  -- P141.upper; P141: lambda=263/200, y=9/8: 3555166/10000000 < L_minus(1+(263/200)/(3080217/1000000)); L_plus(1+(263/200)/(30802167/10000000)) < 3555171/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((30802167 : Rat) / (10000000 : Rat))))))) ((3555171 : Rat)/10000000) .lt,
  -- P142.lower; P142: lambda=263/200, y=75/64: 3417210/10000000 < L_minus(1+(263/200)/(32280397/10000000)); L_plus(1+(263/200)/(16140197/5000000)) < 3417215/10000000.
  Comparison.ofRats ((3417210 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((32280397 : Rat) / (10000000 : Rat))))))) .lt,
  -- P142.upper; P142: lambda=263/200, y=75/64: 3417210/10000000 < L_minus(1+(263/200)/(32280397/10000000)); L_plus(1+(263/200)/(16140197/5000000)) < 3417215/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16140197 : Rat) / (5000000 : Rat))))))) ((3417215 : Rat)/10000000) .lt,
  -- P143.lower; P143: lambda=263/200, y=39/32: 3283773/10000000 < L_minus(1+(263/200)/(16914783/5000000)); L_plus(1+(263/200)/(16914781/5000000)) < 3283778/10000000.
  Comparison.ofRats ((3283773 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16914783 : Rat) / (5000000 : Rat))))))) .lt,
  -- P143.upper; P143: lambda=263/200, y=39/32: 3283773/10000000 < L_minus(1+(263/200)/(16914783/5000000)); L_plus(1+(263/200)/(16914781/5000000)) < 3283778/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((16914781 : Rat) / (5000000 : Rat))))))) ((3283778 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict041
