module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict066

def records : List Comparison := [
  -- A050.den; A050: D=6/5, lambda in [7/8,28/25], y in [9/8,39/32], m=49/100: delta > 557086/1000000 > 0; B_balance > 73491/1000000 > 0.
  Comparison.ofRats ((557086 : Rat)/1000000) ((cellDelta a050)) .lt,
  -- A050.balance; A050: D=6/5, lambda in [7/8,28/25], y in [9/8,39/32], m=49/100: delta > 557086/1000000 > 0; B_balance > 73491/1000000 > 0.
  Comparison.ofRats ((73491 : Rat)/1000000) ((cellBalance a050)) .lt,
  -- A051.den; A051: D=6/5, lambda in [7/8,28/25], y in [39/32,21/16], m=49/100: delta > 534598/1000000 > 0; B_balance > 112250/1000000 > 0.
  Comparison.ofRats ((534598 : Rat)/1000000) ((cellDelta a051)) .lt,
  -- A051.balance; A051: D=6/5, lambda in [7/8,28/25], y in [39/32,21/16], m=49/100: delta > 534598/1000000 > 0; B_balance > 112250/1000000 > 0.
  Comparison.ofRats ((112250 : Rat)/1000000) ((cellBalance a051)) .lt,
  -- A052.den; A052: D=6/5, lambda in [7/8,28/25], y in [21/16,45/32], m=49/100: delta > 518421/1000000 > 0; B_balance > 176032/1000000 > 0.
  Comparison.ofRats ((518421 : Rat)/1000000) ((cellDelta a052)) .lt,
  -- A052.balance; A052: D=6/5, lambda in [7/8,28/25], y in [21/16,45/32], m=49/100: delta > 518421/1000000 > 0; B_balance > 176032/1000000 > 0.
  Comparison.ofRats ((176032 : Rat)/1000000) ((cellBalance a052)) .lt,
  -- A053.den; A053: D=6/5, lambda in [7/8,28/25], y in [45/32,3/2], m=49/100: delta > 509617/1000000 > 0; B_balance > 278803/1000000 > 0.
  Comparison.ofRats ((509617 : Rat)/1000000) ((cellDelta a053)) .lt,
  -- A053.balance; A053: D=6/5, lambda in [7/8,28/25], y in [45/32,3/2], m=49/100: delta > 509617/1000000 > 0; B_balance > 278803/1000000 > 0.
  Comparison.ofRats ((278803 : Rat)/1000000) ((cellBalance a053)) .lt,
  -- A054.den; A054: D=6/5, lambda in [7/8,28/25], y in [3/2,51/32], m=49/100: delta > 509320/1000000 > 0; B_balance > 437939/1000000 > 0.
  Comparison.ofRats ((509320 : Rat)/1000000) ((cellDelta a054)) .lt,
  -- A054.balance; A054: D=6/5, lambda in [7/8,28/25], y in [3/2,51/32], m=49/100: delta > 509320/1000000 > 0; B_balance > 437939/1000000 > 0.
  Comparison.ofRats ((437939 : Rat)/1000000) ((cellBalance a054)) .lt,
  -- A055.den; A055: D=6/5, lambda in [7/8,28/25], y in [51/32,27/16], m=49/100: delta > 518739/1000000 > 0; B_balance > 672658/1000000 > 0.
  Comparison.ofRats ((518739 : Rat)/1000000) ((cellDelta a055)) .lt,
  -- A055.balance; A055: D=6/5, lambda in [7/8,28/25], y in [51/32,27/16], m=49/100: delta > 518739/1000000 > 0; B_balance > 672658/1000000 > 0.
  Comparison.ofRats ((672658 : Rat)/1000000) ((cellBalance a055)) .lt,
  -- A056.den; A056: D=6/5, lambda in [7/8,28/25], y in [27/16,15/8], m=49/100: delta > 423452/1000000 > 0; B_balance > 273588/1000000 > 0.
  Comparison.ofRats ((423452 : Rat)/1000000) ((cellDelta a056)) .lt,
  -- A056.balance; A056: D=6/5, lambda in [7/8,28/25], y in [27/16,15/8], m=49/100: delta > 423452/1000000 > 0; B_balance > 273588/1000000 > 0.
  Comparison.ofRats ((273588 : Rat)/1000000) ((cellBalance a056)) .lt,
  -- A057.den; A057: D=6/5, lambda in [7/8,28/25], y in [15/8,33/16], m=49/100: delta > 501668/1000000 > 0; B_balance > 1345567/1000000 > 0.
  Comparison.ofRats ((501668 : Rat)/1000000) ((cellDelta a057)) .lt,
  -- A057.balance; A057: D=6/5, lambda in [7/8,28/25], y in [15/8,33/16], m=49/100: delta > 501668/1000000 > 0; B_balance > 1345567/1000000 > 0.
  Comparison.ofRats ((1345567 : Rat)/1000000) ((cellBalance a057)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict066
