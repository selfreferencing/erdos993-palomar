module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict029

def records : List Comparison := [
  -- P040.lower; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats ((4535176 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((15248181 : Rat) / (10000000 : Rat))))))) .lt,
  -- P040.upper; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((7624089 : Rat) / (5000000 : Rat))))))) ((4535181 : Rat)/10000000) .lt,
  -- P041.lower; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats ((4366799 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))))) .lt,
  -- P041.upper; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))))) ((4366804 : Rat)/10000000) .lt,
  -- P042.lower; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats ((4203445 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((334937 : Rat) / (200000 : Rat))))))) .lt,
  -- P042.upper; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((16746847 : Rat) / (10000000 : Rat))))))) ((4203450 : Rat)/10000000) .lt,
  -- P043.lower; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats ((4045043 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P043.upper; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((4045049 : Rat)/10000000) .lt,
  -- P044.lower; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats ((3891519 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((1149551 : Rat) / (625000 : Rat))))))) .lt,
  -- P044.upper; P044: lambda=7/8, y=39/64: 3891519/10000000 < L_minus(1+(7/8)/(1149551/625000)); L_plus(1+(7/8)/(18392813/10000000)) < 3891525/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((18392813 : Rat) / (10000000 : Rat))))))) ((3891525 : Rat)/10000000) .lt,
  -- P045.lower; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats ((3742795 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))))) .lt,
  -- P045.upper; P045: lambda=7/8, y=21/32: 3742795/10000000 < L_minus(1+(7/8)/(9637753/5000000)); L_plus(1+(7/8)/(19275503/10000000)) < 3742801/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))))) ((3742801 : Rat)/10000000) .lt,
  -- P046.lower; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats ((3598790 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((20200557 : Rat) / (10000000 : Rat))))))) .lt,
  -- P046.upper; P046: lambda=7/8, y=45/64: 3598790/10000000 < L_minus(1+(7/8)/(20200557/10000000)); L_plus(1+(7/8)/(10100277/5000000)) < 3598795/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((10100277 : Rat) / (5000000 : Rat))))))) ((3598795 : Rat)/10000000) .lt,
  -- P047.lower; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats ((3459417 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P047.upper; P047: lambda=7/8, y=3/4: 3459417/10000000 < L_minus(1+(7/8)/(10585001/5000000)); L_plus(1+(7/8)/(21169999/10000000)) < 3459423/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (8 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((3459423 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict029
