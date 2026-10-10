module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict067

def records : List Comparison := [
  -- A058.den; A058: D=6/5, lambda in [7/8,28/25], y in [33/16,9/4], m=49/100: delta > 642464/1000000 > 0; B_balance > 2991888/1000000 > 0.
  Comparison.ofRats ((642464 : Rat)/1000000) ((cellDelta a058)) .lt,
  -- A058.balance; A058: D=6/5, lambda in [7/8,28/25], y in [33/16,9/4], m=49/100: delta > 642464/1000000 > 0; B_balance > 2991888/1000000 > 0.
  Comparison.ofRats ((2991888 : Rat)/1000000) ((cellBalance a058)) .lt,
  -- A059.den; A059: D=6/5, lambda in [7/8,28/25], y in [9/4,21/8], m=49/100: delta > 624240/1000000 > 0; B_balance > 4017490/1000000 > 0.
  Comparison.ofRats ((624240 : Rat)/1000000) ((cellDelta a059)) .lt,
  -- A059.balance; A059: D=6/5, lambda in [7/8,28/25], y in [9/4,21/8], m=49/100: delta > 624240/1000000 > 0; B_balance > 4017490/1000000 > 0.
  Comparison.ofRats ((4017490 : Rat)/1000000) ((cellBalance a059)) .lt,
  -- A060.den; A060: D=6/5, lambda in [7/8,28/25], y in [21/8,3], m=49/100: delta > 1361431/1000000 > 0; B_balance > 10741904/1000000 > 0.
  Comparison.ofRats ((1361431 : Rat)/1000000) ((cellDelta a060)) .lt,
  -- A060.balance; A060: D=6/5, lambda in [7/8,28/25], y in [21/8,3], m=49/100: delta > 1361431/1000000 > 0; B_balance > 10741904/1000000 > 0.
  Comparison.ofRats ((10741904 : Rat)/1000000) ((cellBalance a060)) .lt,
  -- A061.den; A061: D=6/5, lambda in [28/25,263/200], y in [0,3/8], m=1/3: delta > 785168/1000000 > 0; B_balance > 24875/1000000 > 0.
  Comparison.ofRats ((785168 : Rat)/1000000) ((cellDelta a061)) .lt,
  -- A061.balance; A061: D=6/5, lambda in [28/25,263/200], y in [0,3/8], m=1/3: delta > 785168/1000000 > 0; B_balance > 24875/1000000 > 0.
  Comparison.ofRats ((24875 : Rat)/1000000) ((cellBalance a061)) .lt,
  -- A062.den; A062: D=6/5, lambda in [28/25,263/200], y in [3/8,27/64], m=1/3: delta > 867865/1000000 > 0; B_balance > 35908/1000000 > 0.
  Comparison.ofRats ((867865 : Rat)/1000000) ((cellDelta a062)) .lt,
  -- A062.balance; A062: D=6/5, lambda in [28/25,263/200], y in [3/8,27/64], m=1/3: delta > 867865/1000000 > 0; B_balance > 35908/1000000 > 0.
  Comparison.ofRats ((35908 : Rat)/1000000) ((cellBalance a062)) .lt,
  -- A063.den; A063: D=6/5, lambda in [28/25,263/200], y in [27/64,15/32], m=2/5: delta > 847063/1000000 > 0; B_balance > 7362/1000000 > 0.
  Comparison.ofRats ((847063 : Rat)/1000000) ((cellDelta a063)) .lt,
  -- A063.balance; A063: D=6/5, lambda in [28/25,263/200], y in [27/64,15/32], m=2/5: delta > 847063/1000000 > 0; B_balance > 7362/1000000 > 0.
  Comparison.ofRats ((7362 : Rat)/1000000) ((cellBalance a063)) .lt,
  -- A064.den; A064: D=6/5, lambda in [28/25,263/200], y in [15/32,63/128], m=2/5: delta > 846449/1000000 > 0; B_balance > 6242/1000000 > 0.
  Comparison.ofRats ((846449 : Rat)/1000000) ((cellDelta a064)) .lt,
  -- A064.balance; A064: D=6/5, lambda in [28/25,263/200], y in [15/32,63/128], m=2/5: delta > 846449/1000000 > 0; B_balance > 6242/1000000 > 0.
  Comparison.ofRats ((6242 : Rat)/1000000) ((cellBalance a064)) .lt,
  -- A065.den; A065: D=6/5, lambda in [28/25,263/200], y in [63/128,33/64], m=9/20: delta > 836195/1000000 > 0; B_balance > 1832/1000000 > 0.
  Comparison.ofRats ((836195 : Rat)/1000000) ((cellDelta a065)) .lt,
  -- A065.balance; A065: D=6/5, lambda in [28/25,263/200], y in [63/128,33/64], m=9/20: delta > 836195/1000000 > 0; B_balance > 1832/1000000 > 0.
  Comparison.ofRats ((1832 : Rat)/1000000) ((cellBalance a065)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict067
