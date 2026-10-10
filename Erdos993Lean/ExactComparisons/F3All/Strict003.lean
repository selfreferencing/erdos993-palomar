module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict003

def records : List Comparison := [
  -- F33: [25/24+(81/200)(3/2)]/[(5/12)(7/5)]<10/3    [lambda/gamma, cap 2]
  Comparison.ofRats (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((3 : Rat) / (2 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((7 : Rat) / (5 : Rat))))) (((10 : Rat) / (3 : Rat))) .lt,
  -- F34: [25/24+(81/200)(7/4)]/[(5/12)(8/5)]<10/3    [lambda/gamma, cap 3]
  Comparison.ofRats (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (4 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((8 : Rat) / (5 : Rat))))) (((10 : Rat) / (3 : Rat))) .lt,
  -- F35: [25/24+(81/200)(2)]/[(5/12)(9/5)]<10/3    [lambda/gamma, cap 4]
  Comparison.ofRats (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * (2 : Rat))) / (((5 : Rat) / (12 : Rat)) * ((9 : Rat) / (5 : Rat))))) (((10 : Rat) / (3 : Rat))) .lt,
  -- F36: [25/24+(81/200)(7/3)]/[(5/12)(21/10)]<10/3    [lambda/gamma, cap 5]
  Comparison.ofRats (((((25 : Rat) / (24 : Rat)) + (((81 : Rat) / (200 : Rat)) * ((7 : Rat) / (3 : Rat)))) / (((5 : Rat) / (12 : Rat)) * ((21 : Rat) / (10 : Rat))))) (((10 : Rat) / (3 : Rat))) .lt,
  -- F37: \beta_+(263/200)<21/25    [CA face cover, cap 1]
  Comparison.ofRats (b05.hi) (((21 : Rat) / (25 : Rat))) .lt,
  -- F38: \beta_+(3/2)<23/25    [CA face cover, cap 2]
  Comparison.ofRats (b06.hi) (((23 : Rat) / (25 : Rat))) .lt,
  -- F39: \beta_+(7/4)<51/50    [CA face cover, cap 3]
  Comparison.ofRats (b07.hi) (((51 : Rat) / (50 : Rat))) .lt,
  -- F40: \beta_+(2)<11/10    [CA face cover, cap 4]
  Comparison.ofRats (b08.hi) (((11 : Rat) / (10 : Rat))) .lt,
  -- F41: \beta_+(7/3)<121/100    [CA face cover, cap 5]
  Comparison.ofRats (b09.hi) (((121 : Rat) / (100 : Rat))) .lt,
  -- F42: N_4(263/463,6/5)>1    [childless diagonal, cap 1]
  Comparison.ofRats ((1 : Rat)) ((nFour (((263 : Rat) / (463 : Rat))) (((6 : Rat) / (5 : Rat))))) .lt,
  -- F43: N_5(263/463,6/5)>3    [childless diagonal, cap 1]
  Comparison.ofRats ((3 : Rat)) ((nFive (((263 : Rat) / (463 : Rat))) (((6 : Rat) / (5 : Rat))))) .lt,
  -- F44: N_4(3/5,7/5)>4    [childless diagonal, cap 2]
  Comparison.ofRats ((4 : Rat)) ((nFour (((3 : Rat) / (5 : Rat))) (((7 : Rat) / (5 : Rat))))) .lt,
  -- F45: N_5(3/5,7/5)>5    [childless diagonal, cap 2]
  Comparison.ofRats ((5 : Rat)) ((nFive (((3 : Rat) / (5 : Rat))) (((7 : Rat) / (5 : Rat))))) .lt,
  -- F46: N_4(7/11,8/5)>5    [childless diagonal, cap 3]
  Comparison.ofRats ((5 : Rat)) ((nFour (((7 : Rat) / (11 : Rat))) (((8 : Rat) / (5 : Rat))))) .lt,
  -- F47: N_5(7/11,8/5)>5    [childless diagonal, cap 3]
  Comparison.ofRats ((5 : Rat)) ((nFive (((7 : Rat) / (11 : Rat))) (((8 : Rat) / (5 : Rat))))) .lt,
  -- F48: N_4(2/3,9/5)>7    [childless diagonal, cap 4]
  Comparison.ofRats ((7 : Rat)) ((nFour (((2 : Rat) / (3 : Rat))) (((9 : Rat) / (5 : Rat))))) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict003
