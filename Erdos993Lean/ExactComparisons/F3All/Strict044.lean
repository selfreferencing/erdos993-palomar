module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict044

def records : List Comparison := [
  -- P160.lower; P160: lambda=3/2, y=3/8: 7084951/10000000 < L_minus(1+(3/2)/(3637479/2500000)); L_plus(1+(3/2)/(14549913/10000000)) < 7084960/10000000.
  Comparison.ofRats ((7084951 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P160.upper; P160: lambda=3/2, y=3/8: 7084951/10000000 < L_minus(1+(3/2)/(3637479/2500000)); L_plus(1+(3/2)/(14549913/10000000)) < 7084960/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((7084960 : Rat)/10000000) .lt,
  -- P161.lower; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats ((6662510 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((15840741 : Rat) / (10000000 : Rat))))))) .lt,
  -- P161.upper; P161: lambda=3/2, y=23/50: 6662510/10000000 < L_minus(1+(3/2)/(15840741/10000000)); L_plus(1+(3/2)/(7920369/5000000)) < 6662517/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((7920369 : Rat) / (5000000 : Rat))))))) ((6662517 : Rat)/10000000) .lt,
  -- P162.lower; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats ((6177087 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P162.upper; P162: lambda=3/2, y=9/16: 6177087/10000000 < L_minus(1+(3/2)/(4387637/2500000)); L_plus(1+(3/2)/(3510109/2000000)) < 6177094/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((6177094 : Rat)/10000000) .lt,
  -- P163.lower; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats ((5755956 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((9637753 : Rat) / (5000000 : Rat))))))) .lt,
  -- P163.upper; P163: lambda=3/2, y=21/32: 5755956/10000000 < L_minus(1+(3/2)/(9637753/5000000)); L_plus(1+(3/2)/(19275503/10000000)) < 5755961/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((19275503 : Rat) / (10000000 : Rat))))))) ((5755961 : Rat)/10000000) .lt,
  -- P164.lower; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats ((5609655 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((19937157 : Rat) / (10000000 : Rat))))))) .lt,
  -- P164.upper; P164: lambda=3/2, y=69/100: 5609655/10000000 < L_minus(1+(3/2)/(19937157/10000000)); L_plus(1+(3/2)/(9968577/5000000)) < 5609661/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((9968577 : Rat) / (5000000 : Rat))))))) ((5609661 : Rat)/10000000) .lt,
  -- P165.lower; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats ((5366822 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((21117143 : Rat) / (10000000 : Rat))))))) .lt,
  -- P165.upper; P165: lambda=3/2, y=299/400: 5366822/10000000 < L_minus(1+(3/2)/(21117143/10000000)); L_plus(1+(3/2)/(1055857/500000)) < 5366828/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((1055857 : Rat) / (500000 : Rat))))))) ((5366828 : Rat)/10000000) .lt,
  -- P166.lower; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats ((5356447 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P166.upper; P166: lambda=3/2, y=3/4: 5356447/10000000 < L_minus(1+(3/2)/(10585001/5000000)); L_plus(1+(3/2)/(21169999/10000000)) < 5356452/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((21169999 : Rat) / (10000000 : Rat))))))) ((5356452 : Rat)/10000000) .lt,
  -- P167.lower; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats ((5132016 : Rat)/10000000) ((logLower (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((22366967 : Rat) / (10000000 : Rat))))))) .lt,
  -- P167.upper; P167: lambda=3/2, y=161/200: 5132016/10000000 < L_minus(1+(3/2)/(22366967/10000000)); L_plus(1+(3/2)/(22366963/10000000)) < 5132022/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((3 : Rat) / (2 : Rat)) / ((22366963 : Rat) / (10000000 : Rat))))))) ((5132022 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict044
