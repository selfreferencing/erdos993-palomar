module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict063

def records : List Comparison := [
  -- A026.den; A026: D=6/5, lambda in [3/5,7/8], y in [27/32,15/16], m=49/100: delta > 700115/1000000 > 0; B_balance > 160183/1000000 > 0.
  Comparison.ofRats ((700115 : Rat)/1000000) ((cellDelta a026)) .lt,
  -- A026.balance; A026: D=6/5, lambda in [3/5,7/8], y in [27/32,15/16], m=49/100: delta > 700115/1000000 > 0; B_balance > 160183/1000000 > 0.
  Comparison.ofRats ((160183 : Rat)/1000000) ((cellBalance a026)) .lt,
  -- A027.den; A027: D=6/5, lambda in [3/5,7/8], y in [15/16,9/8], m=49/100: delta > 575004/1000000 > 0; B_balance > 2898/1000000 > 0.
  Comparison.ofRats ((575004 : Rat)/1000000) ((cellDelta a027)) .lt,
  -- A027.balance; A027: D=6/5, lambda in [3/5,7/8], y in [15/16,9/8], m=49/100: delta > 575004/1000000 > 0; B_balance > 2898/1000000 > 0.
  Comparison.ofRats ((2898 : Rat)/1000000) ((cellBalance a027)) .lt,
  -- A028.den; A028: D=6/5, lambda in [3/5,7/8], y in [9/8,21/16], m=49/100: delta > 527502/1000000 > 0; B_balance > 88839/1000000 > 0.
  Comparison.ofRats ((527502 : Rat)/1000000) ((cellDelta a028)) .lt,
  -- A028.balance; A028: D=6/5, lambda in [3/5,7/8], y in [9/8,21/16], m=49/100: delta > 527502/1000000 > 0; B_balance > 88839/1000000 > 0.
  Comparison.ofRats ((88839 : Rat)/1000000) ((cellBalance a028)) .lt,
  -- A029.den; A029: D=6/5, lambda in [3/5,7/8], y in [21/16,3/2], m=49/100: delta > 506285/1000000 > 0; B_balance > 319408/1000000 > 0.
  Comparison.ofRats ((506285 : Rat)/1000000) ((cellDelta a029)) .lt,
  -- A029.balance; A029: D=6/5, lambda in [3/5,7/8], y in [21/16,3/2], m=49/100: delta > 506285/1000000 > 0; B_balance > 319408/1000000 > 0.
  Comparison.ofRats ((319408 : Rat)/1000000) ((cellBalance a029)) .lt,
  -- A030.den; A030: D=6/5, lambda in [3/5,7/8], y in [3/2,27/16], m=49/100: delta > 519694/1000000 > 0; B_balance > 841159/1000000 > 0.
  Comparison.ofRats ((519694 : Rat)/1000000) ((cellDelta a030)) .lt,
  -- A030.balance; A030: D=6/5, lambda in [3/5,7/8], y in [3/2,27/16], m=49/100: delta > 519694/1000000 > 0; B_balance > 841159/1000000 > 0.
  Comparison.ofRats ((841159 : Rat)/1000000) ((cellBalance a030)) .lt,
  -- A031.den; A031: D=6/5, lambda in [3/5,7/8], y in [27/16,15/8], m=49/100: delta > 577227/1000000 > 0; B_balance > 1812656/1000000 > 0.
  Comparison.ofRats ((577227 : Rat)/1000000) ((cellDelta a031)) .lt,
  -- A031.balance; A031: D=6/5, lambda in [3/5,7/8], y in [27/16,15/8], m=49/100: delta > 577227/1000000 > 0; B_balance > 1812656/1000000 > 0.
  Comparison.ofRats ((1812656 : Rat)/1000000) ((cellBalance a031)) .lt,
  -- A032.den; A032: D=6/5, lambda in [3/5,7/8], y in [15/8,9/4], m=49/100: delta > 467613/1000000 > 0; B_balance > 1819255/1000000 > 0.
  Comparison.ofRats ((467613 : Rat)/1000000) ((cellDelta a032)) .lt,
  -- A032.balance; A032: D=6/5, lambda in [3/5,7/8], y in [15/8,9/4], m=49/100: delta > 467613/1000000 > 0; B_balance > 1819255/1000000 > 0.
  Comparison.ofRats ((1819255 : Rat)/1000000) ((cellBalance a032)) .lt,
  -- A033.den; A033: D=6/5, lambda in [3/5,7/8], y in [9/4,3], m=49/100: delta > 468270/1000000 > 0; B_balance > 3823214/1000000 > 0.
  Comparison.ofRats ((468270 : Rat)/1000000) ((cellDelta a033)) .lt,
  -- A033.balance; A033: D=6/5, lambda in [3/5,7/8], y in [9/4,3], m=49/100: delta > 468270/1000000 > 0; B_balance > 3823214/1000000 > 0.
  Comparison.ofRats ((3823214 : Rat)/1000000) ((cellBalance a033)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict063
