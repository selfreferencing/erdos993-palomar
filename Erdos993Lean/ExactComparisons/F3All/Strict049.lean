module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict049

def records : List Comparison := [
  -- P200.lower; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats ((1193544 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P200.upper; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((1193549 : Rat)/10000000) .lt,
  -- P201.lower; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats ((835382 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P201.upper; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (4 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((835389 : Rat)/10000000) .lt,
  -- P202.lower; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats ((8648193 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P202.upper; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((14549913 : Rat) / (10000000 : Rat))))))) ((8648202 : Rat)/10000000) .lt,
  -- P203.lower; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats ((7672793 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((4333133 : Rat) / (2500000 : Rat))))))) .lt,
  -- P203.upper; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((17332529 : Rat) / (10000000 : Rat))))))) ((7672802 : Rat)/10000000) .lt,
  -- P204.lower; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats ((7606022 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P204.upper; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((3510109 : Rat) / (2000000 : Rat))))))) ((7606031 : Rat)/10000000) .lt,
  -- P205.lower; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats ((6959741 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((1242961 : Rat) / (625000 : Rat))))))) .lt,
  -- P205.upper; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((19887373 : Rat) / (10000000 : Rat))))))) ((6959750 : Rat)/10000000) .lt,
  -- P206.lower; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats ((6651243 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((10585001 : Rat) / (5000000 : Rat))))))) .lt,
  -- P206.upper; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((21169999 : Rat) / (10000000 : Rat))))))) ((6651250 : Rat)/10000000) .lt,
  -- P207.lower; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats ((6620930 : Rat)/10000000) ((logLower (((1 : Rat) + ((2 : Rat) / ((21302729 : Rat) / (10000000 : Rat))))))) .lt,
  -- P207.upper; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((2 : Rat) / ((10651363 : Rat) / (5000000 : Rat))))))) ((6620937 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict049
