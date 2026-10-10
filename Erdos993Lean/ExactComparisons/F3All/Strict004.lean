module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict004

def records : List Comparison := [
  -- F49: N_5(2/3,9/5)>5    [childless diagonal, cap 4]
  Comparison.ofRats ((5 : Rat)) ((nFive (((2 : Rat) / (3 : Rat))) (((9 : Rat) / (5 : Rat))))) .lt,
  -- F50: N_4(7/10,21/10)>9    [childless diagonal, cap 5]
  Comparison.ofRats ((9 : Rat)) ((nFour (((7 : Rat) / (10 : Rat))) (((21 : Rat) / (10 : Rat))))) .lt,
  -- F51: N_5(7/10,21/10)>5    [childless diagonal, cap 5]
  Comparison.ofRats ((5 : Rat)) ((nFive (((7 : Rat) / (10 : Rat))) (((21 : Rat) / (10 : Rat))))) .lt,
  -- F52: C(61/20)=-1059/2000<0    [J minimizer left endpoint]
  Comparison.ofRats ((cubicC (((61 : Rat) / (20 : Rat))))) ((0 : Rat)) .lt,
  -- F53: C(123/40)=12147/16000>0    [J minimizer right endpoint]
  Comparison.ofRats ((0 : Rat)) ((cubicC (((123 : Rat) / (40 : Rat))))) .lt,
  -- F54: 2187/1420-153/100=18/1775>0    [J minimum]
  Comparison.ofRats ((0 : Rat)) ((((2187 : Rat) / (1420 : Rat)) - ((153 : Rat) / (100 : Rat)))) .lt,
  -- F55: 20/7-2=6/7>0    [CA child derivative]
  Comparison.ofRats ((0 : Rat)) ((((20 : Rat) / (7 : Rat)) - (2 : Rat))) .lt,
  -- F56: 7/5-21/16=7/80>0    [CA child derivative]
  Comparison.ofRats ((0 : Rat)) ((((7 : Rat) / (5 : Rat)) - ((21 : Rat) / (16 : Rat)))) .lt,
  -- F57: 112/125-154/225=238/1125>0    [CA child derivative]
  Comparison.ofRats ((0 : Rat)) ((((112 : Rat) / (125 : Rat)) - ((154 : Rat) / (225 : Rat)))) .lt,
  -- F58: 16/5+25/32+7/16<9/2    [CA face curvature]
  Comparison.ofRats (((((16 : Rat) / (5 : Rat)) + ((25 : Rat) / (32 : Rat))) + ((7 : Rat) / (16 : Rat)))) (((9 : Rat) / (2 : Rat))) .lt,
  -- F59: (49/100)^2<35/144    [AC splitting parameter]
  Comparison.ofRats ((((49 : Rat) / (100 : Rat)) ^ 2)) (((35 : Rat) / (144 : Rat))) .lt,
  -- F60: 21/25-5/6=1/150>0    [T0 activity derivative]
  Comparison.ofRats ((0 : Rat)) ((((21 : Rat) / (25 : Rat)) - ((5 : Rat) / (6 : Rat)))) .lt,
  -- F61: 1-25/32-147/2048=301/2048>0    [negative L easy case]
  Comparison.ofRats ((0 : Rat)) ((((1 : Rat) - ((25 : Rat) / (32 : Rat))) - ((147 : Rat) / (2048 : Rat)))) .lt,
  -- F62: -19/21+4/3=3/7>0    [childless derivative, y<=1/2]
  Comparison.ofRats ((0 : Rat)) ((((-(19 : Rat)) / (21 : Rat)) + ((4 : Rat) / (3 : Rat)))) .lt,
  -- F63: -19/21+2789/3360+1/3=869/3360>0    [childless derivative, 1/2<=y<=1]
  Comparison.ofRats ((0 : Rat)) (((((-(19 : Rat)) / (21 : Rat)) + ((2789 : Rat) / (3360 : Rat))) + ((1 : Rat) / (3 : Rat)))) .lt,
  -- F64: 32/7-491/240-50/21=81/560>0    [childless derivative, y>=1]
  Comparison.ofRats ((0 : Rat)) (((((32 : Rat) / (7 : Rat)) - ((491 : Rat) / (240 : Rat))) - ((50 : Rat) / (21 : Rat)))) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict004
