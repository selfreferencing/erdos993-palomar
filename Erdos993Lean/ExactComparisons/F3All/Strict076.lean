module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict076

def records : List Comparison := [
  -- A130.den; A130: D=8/5, lambda in [3/2,7/4], y in [3/2,27/16], m=49/100: delta > 422005/1000000 > 0; B_balance > 227787/1000000 > 0.
  Comparison.ofRats ((422005 : Rat)/1000000) ((cellDelta a130)) .lt,
  -- A130.balance; A130: D=8/5, lambda in [3/2,7/4], y in [3/2,27/16], m=49/100: delta > 422005/1000000 > 0; B_balance > 227787/1000000 > 0.
  Comparison.ofRats ((227787 : Rat)/1000000) ((cellBalance a130)) .lt,
  -- A131.den; A131: D=8/5, lambda in [3/2,7/4], y in [27/16,15/8], m=49/100: delta > 433630/1000000 > 0; B_balance > 474688/1000000 > 0.
  Comparison.ofRats ((433630 : Rat)/1000000) ((cellDelta a131)) .lt,
  -- A131.balance; A131: D=8/5, lambda in [3/2,7/4], y in [27/16,15/8], m=49/100: delta > 433630/1000000 > 0; B_balance > 474688/1000000 > 0.
  Comparison.ofRats ((474688 : Rat)/1000000) ((cellBalance a131)) .lt,
  -- A132.den; A132: D=8/5, lambda in [3/2,7/4], y in [15/8,33/16], m=49/100: delta > 486734/1000000 > 0; B_balance > 970117/1000000 > 0.
  Comparison.ofRats ((486734 : Rat)/1000000) ((cellDelta a132)) .lt,
  -- A132.balance; A132: D=8/5, lambda in [3/2,7/4], y in [15/8,33/16], m=49/100: delta > 486734/1000000 > 0; B_balance > 970117/1000000 > 0.
  Comparison.ofRats ((970117 : Rat)/1000000) ((cellBalance a132)) .lt,
  -- A133.den; A133: D=8/5, lambda in [3/2,7/4], y in [33/16,9/4], m=49/100: delta > 592286/1000000 > 0; B_balance > 1778312/1000000 > 0.
  Comparison.ofRats ((592286 : Rat)/1000000) ((cellDelta a133)) .lt,
  -- A133.balance; A133: D=8/5, lambda in [3/2,7/4], y in [33/16,9/4], m=49/100: delta > 592286/1000000 > 0; B_balance > 1778312/1000000 > 0.
  Comparison.ofRats ((1778312 : Rat)/1000000) ((cellBalance a133)) .lt,
  -- A134.den; A134: D=8/5, lambda in [3/2,7/4], y in [9/4,21/8], m=49/100: delta > 542322/1000000 > 0; B_balance > 2213078/1000000 > 0.
  Comparison.ofRats ((542322 : Rat)/1000000) ((cellDelta a134)) .lt,
  -- A134.balance; A134: D=8/5, lambda in [3/2,7/4], y in [9/4,21/8], m=49/100: delta > 542322/1000000 > 0; B_balance > 2213078/1000000 > 0.
  Comparison.ofRats ((2213078 : Rat)/1000000) ((cellBalance a134)) .lt,
  -- A135.den; A135: D=8/5, lambda in [3/2,7/4], y in [21/8,3], m=49/100: delta > 1141838/1000000 > 0; B_balance > 5960044/1000000 > 0.
  Comparison.ofRats ((1141838 : Rat)/1000000) ((cellDelta a135)) .lt,
  -- A135.balance; A135: D=8/5, lambda in [3/2,7/4], y in [21/8,3], m=49/100: delta > 1141838/1000000 > 0; B_balance > 5960044/1000000 > 0.
  Comparison.ofRats ((5960044 : Rat)/1000000) ((cellBalance a135)) .lt,
  -- A136.den; A136: D=9/5, lambda in [7/4,2], y in [0,3/8], m=1/3: delta > 777969/1000000 > 0; B_balance > 162481/1000000 > 0.
  Comparison.ofRats ((777969 : Rat)/1000000) ((cellDelta a136)) .lt,
  -- A136.balance; A136: D=9/5, lambda in [7/4,2], y in [0,3/8], m=1/3: delta > 777969/1000000 > 0; B_balance > 162481/1000000 > 0.
  Comparison.ofRats ((162481 : Rat)/1000000) ((cellBalance a136)) .lt,
  -- A137.den; A137: D=9/5, lambda in [7/4,2], y in [3/8,9/16], m=1/3: delta > 757675/1000000 > 0; B_balance > 100187/1000000 > 0.
  Comparison.ofRats ((757675 : Rat)/1000000) ((cellDelta a137)) .lt,
  -- A137.balance; A137: D=9/5, lambda in [7/4,2], y in [3/8,9/16], m=1/3: delta > 757675/1000000 > 0; B_balance > 100187/1000000 > 0.
  Comparison.ofRats ((100187 : Rat)/1000000) ((cellBalance a137)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict076
