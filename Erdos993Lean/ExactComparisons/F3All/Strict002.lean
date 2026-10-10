module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict002

def records : List Comparison := [
  -- F17: 1-(267809/60000)/(181/40)-(263/200)^2(3/8)^{4}/4>0    [negative L, cap 1]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - (((267809 : Rat) / (60000 : Rat)) / ((181 : Rat) / (40 : Rat)))) - (((((263 : Rat) / (200 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 4)) / (4 : Rat)))) .lt,
  -- F18: E_5(9733/6058)>49/10    [negative L, cap 2]
  Comparison.ofRats (((49 : Rat) / (10 : Rat))) ((expFive (((9733 : Rat) / (6058 : Rat))))) .lt,
  -- F19: 1-(3029/700)/(49/10)-(3/2)^2(3/8)^{4}/4>0    [negative L, cap 2]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - (((3029 : Rat) / (700 : Rat)) / ((49 : Rat) / (10 : Rat)))) - (((((3 : Rat) / (2 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 4)) / (4 : Rat)))) .lt,
  -- F20: E_5(11201/7001)>49/10    [negative L, cap 3]
  Comparison.ofRats (((49 : Rat) / (10 : Rat))) ((expFive (((11201 : Rat) / (7001 : Rat))))) .lt,
  -- F21: 1-(7001/1600)/(49/10)-(7/4)^2(3/8)^{3}/4>0    [negative L, cap 3]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - (((7001 : Rat) / (1600 : Rat)) / ((49 : Rat) / (10 : Rat)))) - (((((7 : Rat) / (4 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) .lt,
  -- F22: E_5(3361/2011)>21/4    [negative L, cap 4]
  Comparison.ofRats (((21 : Rat) / (4 : Rat))) ((expFive (((3361 : Rat) / (2011 : Rat))))) .lt,
  -- F23: 1-(2011/450)/(21/4)-(2)^2(3/8)^{3}/4>0    [negative L, cap 4]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - (((2011 : Rat) / (450 : Rat)) / ((21 : Rat) / (4 : Rat)))) - ((((2 : Rat) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) .lt,
  -- F24: E_5(8509/4834)>23/4    [negative L, cap 5]
  Comparison.ofRats (((23 : Rat) / (4 : Rat))) ((expFive (((8509 : Rat) / (4834 : Rat))))) .lt,
  -- F25: 1-(2417/525)/(23/4)-(7/3)^2(3/8)^{3}/4>0    [negative L, cap 5]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - (((2417 : Rat) / (525 : Rat)) / ((23 : Rat) / (4 : Rat)))) - (((((7 : Rat) / (3 : Rat)) ^ 2) * (((3 : Rat) / (8 : Rat)) ^ 3)) / (4 : Rat)))) .lt,
  -- F26: (4097/1500)(7/8)+[(4097/1500)(1-7/8)+(4/5)/2]^2/[4(4097/1500+(4/5)/4)]<8/3    [ell decreases in lambda, row 1]
  Comparison.ofRats (((((4097 : Rat) / (1500 : Rat)) * ((7 : Rat) / (8 : Rat))) + ((((((4097 : Rat) / (1500 : Rat)) * ((1 : Rat) - ((7 : Rat) / (8 : Rat)))) + (((4 : Rat) / (5 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((4097 : Rat) / (1500 : Rat)) + (((4 : Rat) / (5 : Rat)) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F27: (188909/60000)(7/9)+[(188909/60000)(1-7/9)+(263/200)/2]^2/[4(188909/60000+(263/200)/4)]<8/3    [ell decreases in lambda, row 2]
  Comparison.ofRats (((((188909 : Rat) / (60000 : Rat)) * ((7 : Rat) / (9 : Rat))) + ((((((188909 : Rat) / (60000 : Rat)) * ((1 : Rat) - ((7 : Rat) / (9 : Rat)))) + (((263 : Rat) / (200 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((188909 : Rat) / (60000 : Rat)) + (((263 : Rat) / (200 : Rat)) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F28: (1979/700)(663/926)+[(1979/700)(1-663/926)+(3/2)/2]^2/[4(1979/700+(3/2)/4)]<8/3    [ell decreases in lambda, row 3]
  Comparison.ofRats (((((1979 : Rat) / (700 : Rat)) * ((663 : Rat) / (926 : Rat))) + ((((((1979 : Rat) / (700 : Rat)) * ((1 : Rat) - ((663 : Rat) / (926 : Rat)))) + (((3 : Rat) / (2 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1979 : Rat) / (700 : Rat)) + (((3 : Rat) / (2 : Rat)) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F29: (4201/1600)(7/10)+[(4201/1600)(1-7/10)+(7/4)/2]^2/[4(4201/1600+(7/4)/4)]<8/3    [ell decreases in lambda, row 4]
  Comparison.ofRats (((((4201 : Rat) / (1600 : Rat)) * ((7 : Rat) / (10 : Rat))) + ((((((4201 : Rat) / (1600 : Rat)) * ((1 : Rat) - ((7 : Rat) / (10 : Rat)))) + (((7 : Rat) / (4 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((4201 : Rat) / (1600 : Rat)) + (((7 : Rat) / (4 : Rat)) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F30: (1111/450)(15/22)+[(1111/450)(1-15/22)+(2)/2]^2/[4(1111/450+(2)/4)]<8/3    [ell decreases in lambda, row 5]
  Comparison.ofRats (((((1111 : Rat) / (450 : Rat)) * ((15 : Rat) / (22 : Rat))) + ((((((1111 : Rat) / (450 : Rat)) * ((1 : Rat) - ((15 : Rat) / (22 : Rat)))) + ((2 : Rat) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1111 : Rat) / (450 : Rat)) + ((2 : Rat) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F31: (1192/525)(2/3)+[(1192/525)(1-2/3)+(7/3)/2]^2/[4(1192/525+(7/3)/4)]<8/3    [ell decreases in lambda, row 6]
  Comparison.ofRats (((((1192 : Rat) / (525 : Rat)) * ((2 : Rat) / (3 : Rat))) + ((((((1192 : Rat) / (525 : Rat)) * ((1 : Rat) - ((2 : Rat) / (3 : Rat)))) + (((7 : Rat) / (3 : Rat)) / (2 : Rat))) ^ 2) / ((4 : Rat) * (((1192 : Rat) / (525 : Rat)) + (((7 : Rat) / (3 : Rat)) / (4 : Rat))))))) (((8 : Rat) / (3 : Rat))) .lt,
  -- F32: [25/24+(81/200)(263/200)]/[(5/12)(6/5)]<10/3    [lambda/gamma, cap 1]
  Comparison.ofRats (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((263 : Rat) / (200 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((6 : Rat) / (5 : Rat))))) (((10 : Rat) / (3 : Rat))) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict002
