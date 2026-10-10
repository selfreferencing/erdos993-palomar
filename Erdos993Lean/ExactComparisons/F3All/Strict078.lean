module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict078

def records : List Comparison := [
  -- A146.den; A146: D=9/5, lambda in [7/4,2], y in [33/16,9/4], m=49/100: delta > 576538/1000000 > 0; B_balance > 1539352/1000000 > 0.
  Comparison.ofRats ((576538 : Rat)/1000000) ((cellDelta a146)) .lt,
  -- A146.balance; A146: D=9/5, lambda in [7/4,2], y in [33/16,9/4], m=49/100: delta > 576538/1000000 > 0; B_balance > 1539352/1000000 > 0.
  Comparison.ofRats ((1539352 : Rat)/1000000) ((cellBalance a146)) .lt,
  -- A147.den; A147: D=9/5, lambda in [7/4,2], y in [9/4,21/8], m=49/100: delta > 518593/1000000 > 0; B_balance > 1872336/1000000 > 0.
  Comparison.ofRats ((518593 : Rat)/1000000) ((cellDelta a147)) .lt,
  -- A147.balance; A147: D=9/5, lambda in [7/4,2], y in [9/4,21/8], m=49/100: delta > 518593/1000000 > 0; B_balance > 1872336/1000000 > 0.
  Comparison.ofRats ((1872336 : Rat)/1000000) ((cellBalance a147)) .lt,
  -- A148.den; A148: D=9/5, lambda in [7/4,2], y in [21/8,3], m=49/100: delta > 1077056/1000000 > 0; B_balance > 4993081/1000000 > 0.
  Comparison.ofRats ((1077056 : Rat)/1000000) ((cellDelta a148)) .lt,
  -- A148.balance; A148: D=9/5, lambda in [7/4,2], y in [21/8,3], m=49/100: delta > 1077056/1000000 > 0; B_balance > 4993081/1000000 > 0.
  Comparison.ofRats ((4993081 : Rat)/1000000) ((cellBalance a148)) .lt,
  -- A149.den; A149: D=21/10, lambda in [2,7/3], y in [0,3/8], m=0: delta > 762007/1000000 > 0; B_balance > 187702/1000000 > 0.
  Comparison.ofRats ((762007 : Rat)/1000000) ((cellDelta a149)) .lt,
  -- A149.balance; A149: D=21/10, lambda in [2,7/3], y in [0,3/8], m=0: delta > 762007/1000000 > 0; B_balance > 187702/1000000 > 0.
  Comparison.ofRats ((187702 : Rat)/1000000) ((cellBalance a149)) .lt,
  -- A150.den; A150: D=21/10, lambda in [2,7/3], y in [3/8,3/4], m=2/5: delta > 612091/1000000 > 0; B_balance > 29637/1000000 > 0.
  Comparison.ofRats ((612091 : Rat)/1000000) ((cellDelta a150)) .lt,
  -- A150.balance; A150: D=21/10, lambda in [2,7/3], y in [3/8,3/4], m=2/5: delta > 612091/1000000 > 0; B_balance > 29637/1000000 > 0.
  Comparison.ofRats ((29637 : Rat)/1000000) ((cellBalance a150)) .lt,
  -- A151.den; A151: D=21/10, lambda in [2,7/3], y in [3/4,9/8], m=49/100: delta > 451196/1000000 > 0; B_balance > 5967/1000000 > 0.
  Comparison.ofRats ((451196 : Rat)/1000000) ((cellDelta a151)) .lt,
  -- A151.balance; A151: D=21/10, lambda in [2,7/3], y in [3/4,9/8], m=49/100: delta > 451196/1000000 > 0; B_balance > 5967/1000000 > 0.
  Comparison.ofRats ((5967 : Rat)/1000000) ((cellBalance a151)) .lt,
  -- A152.den; A152: D=21/10, lambda in [2,7/3], y in [9/8,21/16], m=49/100: delta > 488183/1000000 > 0; B_balance > 152603/1000000 > 0.
  Comparison.ofRats ((488183 : Rat)/1000000) ((cellDelta a152)) .lt,
  -- A152.balance; A152: D=21/10, lambda in [2,7/3], y in [9/8,21/16], m=49/100: delta > 488183/1000000 > 0; B_balance > 152603/1000000 > 0.
  Comparison.ofRats ((152603 : Rat)/1000000) ((cellBalance a152)) .lt,
  -- A153.den; A153: D=21/10, lambda in [2,7/3], y in [21/16,3/2], m=49/100: delta > 444172/1000000 > 0; B_balance > 202684/1000000 > 0.
  Comparison.ofRats ((444172 : Rat)/1000000) ((cellDelta a153)) .lt,
  -- A153.balance; A153: D=21/10, lambda in [2,7/3], y in [21/16,3/2], m=49/100: delta > 444172/1000000 > 0; B_balance > 202684/1000000 > 0.
  Comparison.ofRats ((202684 : Rat)/1000000) ((cellBalance a153)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict078
