module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict061

def records : List Comparison := [
  -- A010.den; A010: D=6/5, lambda in [1/3,3/5], y in [15/16,9/8], m=49/100: delta > 660453/1000000 > 0; B_balance > 411161/1000000 > 0.
  Comparison.ofRats ((660453 : Rat)/1000000) ((cellDelta a010)) .lt,
  -- A010.balance; A010: D=6/5, lambda in [1/3,3/5], y in [15/16,9/8], m=49/100: delta > 660453/1000000 > 0; B_balance > 411161/1000000 > 0.
  Comparison.ofRats ((411161 : Rat)/1000000) ((cellBalance a010)) .lt,
  -- A011.den; A011: D=6/5, lambda in [1/3,3/5], y in [9/8,21/16], m=49/100: delta > 637637/1000000 > 0; B_balance > 815835/1000000 > 0.
  Comparison.ofRats ((637637 : Rat)/1000000) ((cellDelta a011)) .lt,
  -- A011.balance; A011: D=6/5, lambda in [1/3,3/5], y in [9/8,21/16], m=49/100: delta > 637637/1000000 > 0; B_balance > 815835/1000000 > 0.
  Comparison.ofRats ((815835 : Rat)/1000000) ((cellBalance a011)) .lt,
  -- A012.den; A012: D=6/5, lambda in [1/3,3/5], y in [21/16,3/2], m=49/100: delta > 646131/1000000 > 0; B_balance > 1522942/1000000 > 0.
  Comparison.ofRats ((646131 : Rat)/1000000) ((cellDelta a012)) .lt,
  -- A012.balance; A012: D=6/5, lambda in [1/3,3/5], y in [21/16,3/2], m=49/100: delta > 646131/1000000 > 0; B_balance > 1522942/1000000 > 0.
  Comparison.ofRats ((1522942 : Rat)/1000000) ((cellBalance a012)) .lt,
  -- A013.den; A013: D=6/5, lambda in [1/3,3/5], y in [3/2,15/8], m=49/100: delta > 490783/1000000 > 0; B_balance > 1312916/1000000 > 0.
  Comparison.ofRats ((490783 : Rat)/1000000) ((cellDelta a013)) .lt,
  -- A013.balance; A013: D=6/5, lambda in [1/3,3/5], y in [3/2,15/8], m=49/100: delta > 490783/1000000 > 0; B_balance > 1312916/1000000 > 0.
  Comparison.ofRats ((1312916 : Rat)/1000000) ((cellBalance a013)) .lt,
  -- A014.den; A014: D=6/5, lambda in [1/3,3/5], y in [15/8,9/4], m=49/100: delta > 746242/1000000 > 0; B_balance > 5916806/1000000 > 0.
  Comparison.ofRats ((746242 : Rat)/1000000) ((cellDelta a014)) .lt,
  -- A014.balance; A014: D=6/5, lambda in [1/3,3/5], y in [15/8,9/4], m=49/100: delta > 746242/1000000 > 0; B_balance > 5916806/1000000 > 0.
  Comparison.ofRats ((5916806 : Rat)/1000000) ((cellBalance a014)) .lt,
  -- A015.den; A015: D=6/5, lambda in [1/3,3/5], y in [9/4,3], m=49/100: delta > 895931/1000000 > 0; B_balance > 11479831/1000000 > 0.
  Comparison.ofRats ((895931 : Rat)/1000000) ((cellDelta a015)) .lt,
  -- A015.balance; A015: D=6/5, lambda in [1/3,3/5], y in [9/4,3], m=49/100: delta > 895931/1000000 > 0; B_balance > 11479831/1000000 > 0.
  Comparison.ofRats ((11479831 : Rat)/1000000) ((cellBalance a015)) .lt,
  -- A016.den; A016: D=6/5, lambda in [3/5,7/8], y in [0,3/16], m=1/3: delta > 970364/1000000 > 0; B_balance > 111405/1000000 > 0.
  Comparison.ofRats ((970364 : Rat)/1000000) ((cellDelta a016)) .lt,
  -- A016.balance; A016: D=6/5, lambda in [3/5,7/8], y in [0,3/16], m=1/3: delta > 970364/1000000 > 0; B_balance > 111405/1000000 > 0.
  Comparison.ofRats ((111405 : Rat)/1000000) ((cellBalance a016)) .lt,
  -- A017.den; A017: D=6/5, lambda in [3/5,7/8], y in [3/16,9/32], m=1/3: delta > 958963/1000000 > 0; B_balance > 30673/1000000 > 0.
  Comparison.ofRats ((958963 : Rat)/1000000) ((cellDelta a017)) .lt,
  -- A017.balance; A017: D=6/5, lambda in [3/5,7/8], y in [3/16,9/32], m=1/3: delta > 958963/1000000 > 0; B_balance > 30673/1000000 > 0.
  Comparison.ofRats ((30673 : Rat)/1000000) ((cellBalance a017)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict061
