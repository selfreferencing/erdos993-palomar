module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict077

def records : List Comparison := [
  -- A138.den; A138: D=9/5, lambda in [7/4,2], y in [9/16,3/4], m=9/20: delta > 687717/1000000 > 0; B_balance > 48845/1000000 > 0.
  Comparison.ofRats ((687717 : Rat)/1000000) ((cellDelta a138)) .lt,
  -- A138.balance; A138: D=9/5, lambda in [7/4,2], y in [9/16,3/4], m=9/20: delta > 687717/1000000 > 0; B_balance > 48845/1000000 > 0.
  Comparison.ofRats ((48845 : Rat)/1000000) ((cellBalance a138)) .lt,
  -- A139.den; A139: D=9/5, lambda in [7/4,2], y in [3/4,15/16], m=49/100: delta > 617489/1000000 > 0; B_balance > 71100/1000000 > 0.
  Comparison.ofRats ((617489 : Rat)/1000000) ((cellDelta a139)) .lt,
  -- A139.balance; A139: D=9/5, lambda in [7/4,2], y in [3/4,15/16], m=49/100: delta > 617489/1000000 > 0; B_balance > 71100/1000000 > 0.
  Comparison.ofRats ((71100 : Rat)/1000000) ((cellBalance a139)) .lt,
  -- A140.den; A140: D=9/5, lambda in [7/4,2], y in [15/16,9/8], m=49/100: delta > 550535/1000000 > 0; B_balance > 100412/1000000 > 0.
  Comparison.ofRats ((550535 : Rat)/1000000) ((cellDelta a140)) .lt,
  -- A140.balance; A140: D=9/5, lambda in [7/4,2], y in [15/16,9/8], m=49/100: delta > 550535/1000000 > 0; B_balance > 100412/1000000 > 0.
  Comparison.ofRats ((100412 : Rat)/1000000) ((cellBalance a140)) .lt,
  -- A141.den; A141: D=9/5, lambda in [7/4,2], y in [9/8,21/16], m=49/100: delta > 492344/1000000 > 0; B_balance > 135920/1000000 > 0.
  Comparison.ofRats ((492344 : Rat)/1000000) ((cellDelta a141)) .lt,
  -- A141.balance; A141: D=9/5, lambda in [7/4,2], y in [9/8,21/16], m=49/100: delta > 492344/1000000 > 0; B_balance > 135920/1000000 > 0.
  Comparison.ofRats ((135920 : Rat)/1000000) ((cellBalance a141)) .lt,
  -- A142.den; A142: D=9/5, lambda in [7/4,2], y in [21/16,3/2], m=49/100: delta > 448823/1000000 > 0; B_balance > 186645/1000000 > 0.
  Comparison.ofRats ((448823 : Rat)/1000000) ((cellDelta a142)) .lt,
  -- A142.balance; A142: D=9/5, lambda in [7/4,2], y in [21/16,3/2], m=49/100: delta > 448823/1000000 > 0; B_balance > 186645/1000000 > 0.
  Comparison.ofRats ((186645 : Rat)/1000000) ((cellBalance a142)) .lt,
  -- A143.den; A143: D=9/5, lambda in [7/4,2], y in [3/2,27/16], m=49/100: delta > 426888/1000000 > 0; B_balance > 283665/1000000 > 0.
  Comparison.ofRats ((426888 : Rat)/1000000) ((cellDelta a143)) .lt,
  -- A143.balance; A143: D=9/5, lambda in [7/4,2], y in [3/2,27/16], m=49/100: delta > 426888/1000000 > 0; B_balance > 283665/1000000 > 0.
  Comparison.ofRats ((283665 : Rat)/1000000) ((cellBalance a143)) .lt,
  -- A144.den; A144: D=9/5, lambda in [7/4,2], y in [27/16,15/8], m=49/100: delta > 434520/1000000 > 0; B_balance > 490149/1000000 > 0.
  Comparison.ofRats ((434520 : Rat)/1000000) ((cellDelta a144)) .lt,
  -- A144.balance; A144: D=9/5, lambda in [7/4,2], y in [27/16,15/8], m=49/100: delta > 434520/1000000 > 0; B_balance > 490149/1000000 > 0.
  Comparison.ofRats ((490149 : Rat)/1000000) ((cellBalance a144)) .lt,
  -- A145.den; A145: D=9/5, lambda in [7/4,2], y in [15/8,33/16], m=49/100: delta > 480889/1000000 > 0; B_balance > 887820/1000000 > 0.
  Comparison.ofRats ((480889 : Rat)/1000000) ((cellDelta a145)) .lt,
  -- A145.balance; A145: D=9/5, lambda in [7/4,2], y in [15/8,33/16], m=49/100: delta > 480889/1000000 > 0; B_balance > 887820/1000000 > 0.
  Comparison.ofRats ((887820 : Rat)/1000000) ((cellBalance a145)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict077
