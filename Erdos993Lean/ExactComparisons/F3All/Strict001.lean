module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict001

def records : List Comparison := [
  -- F01: S(1/9)>2231434/10^7    [log(5/4)]
  Comparison.ofRats (((2231434 : Rat) / ((10 : Rat) ^ 7))) ((seriesS (((1 : Rat) / (9 : Rat))))) .lt,
  -- F02: T(1/9)<2231436/10^7    [log(5/4)]
  Comparison.ofRats ((seriesT (((1 : Rat) / (9 : Rat))))) (((2231436 : Rat) / ((10 : Rat) ^ 7))) .lt,
  -- F03: S(1/9)+S(1/11)>4054650/10^7    [log(3/2)]
  Comparison.ofRats (((4054650 : Rat) / ((10 : Rat) ^ 7))) (((seriesS (((1 : Rat) / (9 : Rat)))) + (seriesS (((1 : Rat) / (11 : Rat)))))) .lt,
  -- F04: T(1/9)+T(1/11)<4054652/10^7    [log(3/2)]
  Comparison.ofRats (((seriesT (((1 : Rat) / (9 : Rat)))) + (seriesT (((1 : Rat) / (11 : Rat)))))) (((4054652 : Rat) / ((10 : Rat) ^ 7))) .lt,
  -- F05: S(1/9)+S(1/11)+S(1/7)>6931467/10^7    [log 2]
  Comparison.ofRats (((6931467 : Rat) / ((10 : Rat) ^ 7))) ((((seriesS (((1 : Rat) / (9 : Rat)))) + (seriesS (((1 : Rat) / (11 : Rat))))) + (seriesS (((1 : Rat) / (7 : Rat)))))) .lt,
  -- F06: T(1/9)+T(1/11)+T(1/7)<6931472/10^7    [log 2]
  Comparison.ofRats ((((seriesT (((1 : Rat) / (9 : Rat)))) + (seriesT (((1 : Rat) / (11 : Rat))))) + (seriesT (((1 : Rat) / (7 : Rat)))))) (((6931472 : Rat) / ((10 : Rat) ^ 7))) .lt,
  -- F07: 1/[2(6931467/10^7)^2]<25/24    [affine intercept]
  Comparison.ofRats (((1 : Rat) / ((2 : Rat) * (((6931467 : Rat) / ((10 : Rat) ^ 7)) ^ 2)))) (((25 : Rat) / (24 : Rat))) .lt,
  -- F08: 1/(6931472/10^7)-1/[2(6931472/10^7)^2]<81/200    [affine slope]
  Comparison.ofRats ((((1 : Rat) / ((6931472 : Rat) / ((10 : Rat) ^ 7))) - ((1 : Rat) / ((2 : Rat) * (((6931472 : Rat) / ((10 : Rat) ^ 7)) ^ 2))))) (((81 : Rat) / (200 : Rat))) .lt,
  -- F09: \mathcal L_-(10/3)>7/6    [two child monotonicities]
  Comparison.ofRats (((7 : Rat) / (6 : Rat))) ((logLower (((10 : Rat) / (3 : Rat))))) .lt,
  -- F10: \mathcal L_+(369/80)<153/100    [J below 1/3]
  Comparison.ofRats ((logUpper (((369 : Rat) / (80 : Rat))))) (((153 : Rat) / (100 : Rat))) .lt,
  -- F11: \mathcal L_-(463/200)>4/5    [gamma at cap endpoints]
  Comparison.ofRats (((4 : Rat) / (5 : Rat))) ((logLower (((463 : Rat) / (200 : Rat))))) .lt,
  -- F12: \mathcal E_+(5/4)<4    [CA face curvature]
  Comparison.ofRats ((expUpper (((5 : Rat) / (4 : Rat))))) ((4 : Rat)) .lt,
  -- F13: 6931472/10^7<7/10    [small activity child derivative]
  Comparison.ofRats (((6931472 : Rat) / ((10 : Rat) ^ 7))) (((7 : Rat) / (10 : Rat))) .lt,
  -- F14: 120-60-1=59>0    [Pade denominator]
  Comparison.ofRats ((0 : Rat)) ((((120 : Rat) - (60 : Rat)) - (1 : Rat))) .lt,
  -- F15: 1680-840-20=820>0    [Pade denominator]
  Comparison.ofRats ((0 : Rat)) ((((1680 : Rat) - (840 : Rat)) - (20 : Rat))) .lt,
  -- F16: E_5(405884/267809)>181/40    [negative L, cap 1]
  Comparison.ofRats (((181 : Rat) / (40 : Rat))) ((expFive (((405884 : Rat) / (267809 : Rat))))) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict001
