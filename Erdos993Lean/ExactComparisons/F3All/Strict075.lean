module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict075

def records : List Comparison := [
  -- A122.den; A122: D=7/5, lambda in [263/200,3/2], y in [21/8,3], m=49/100: delta > 1185938/1000000 > 0; B_balance > 7247053/1000000 > 0.
  Comparison.ofRats ((1185938 : Rat)/1000000) ((cellDelta a122)) .lt,
  -- A122.balance; A122: D=7/5, lambda in [263/200,3/2], y in [21/8,3], m=49/100: delta > 1185938/1000000 > 0; B_balance > 7247053/1000000 > 0.
  Comparison.ofRats ((7247053 : Rat)/1000000) ((cellBalance a122)) .lt,
  -- A123.den; A123: D=8/5, lambda in [3/2,7/4], y in [0,3/8], m=1/3: delta > 787254/1000000 > 0; B_balance > 134400/1000000 > 0.
  Comparison.ofRats ((787254 : Rat)/1000000) ((cellDelta a123)) .lt,
  -- A123.balance; A123: D=8/5, lambda in [3/2,7/4], y in [0,3/8], m=1/3: delta > 787254/1000000 > 0; B_balance > 134400/1000000 > 0.
  Comparison.ofRats ((134400 : Rat)/1000000) ((cellBalance a123)) .lt,
  -- A124.den; A124: D=8/5, lambda in [3/2,7/4], y in [3/8,9/16], m=1/3: delta > 764369/1000000 > 0; B_balance > 53565/1000000 > 0.
  Comparison.ofRats ((764369 : Rat)/1000000) ((cellDelta a124)) .lt,
  -- A124.balance; A124: D=8/5, lambda in [3/2,7/4], y in [3/8,9/16], m=1/3: delta > 764369/1000000 > 0; B_balance > 53565/1000000 > 0.
  Comparison.ofRats ((53565 : Rat)/1000000) ((cellBalance a124)) .lt,
  -- A125.den; A125: D=8/5, lambda in [3/2,7/4], y in [9/16,3/4], m=49/100: delta > 689674/1000000 > 0; B_balance > 30535/1000000 > 0.
  Comparison.ofRats ((689674 : Rat)/1000000) ((cellDelta a125)) .lt,
  -- A125.balance; A125: D=8/5, lambda in [3/2,7/4], y in [9/16,3/4], m=49/100: delta > 689674/1000000 > 0; B_balance > 30535/1000000 > 0.
  Comparison.ofRats ((30535 : Rat)/1000000) ((cellBalance a125)) .lt,
  -- A126.den; A126: D=8/5, lambda in [3/2,7/4], y in [3/4,15/16], m=49/100: delta > 616476/1000000 > 0; B_balance > 49185/1000000 > 0.
  Comparison.ofRats ((616476 : Rat)/1000000) ((cellDelta a126)) .lt,
  -- A126.balance; A126: D=8/5, lambda in [3/2,7/4], y in [3/4,15/16], m=49/100: delta > 616476/1000000 > 0; B_balance > 49185/1000000 > 0.
  Comparison.ofRats ((49185 : Rat)/1000000) ((cellBalance a126)) .lt,
  -- A127.den; A127: D=8/5, lambda in [3/2,7/4], y in [15/16,9/8], m=49/100: delta > 546430/1000000 > 0; B_balance > 68700/1000000 > 0.
  Comparison.ofRats ((546430 : Rat)/1000000) ((cellDelta a127)) .lt,
  -- A127.balance; A127: D=8/5, lambda in [3/2,7/4], y in [15/16,9/8], m=49/100: delta > 546430/1000000 > 0; B_balance > 68700/1000000 > 0.
  Comparison.ofRats ((68700 : Rat)/1000000) ((cellBalance a127)) .lt,
  -- A128.den; A128: D=8/5, lambda in [3/2,7/4], y in [9/8,21/16], m=49/100: delta > 486214/1000000 > 0; B_balance > 90358/1000000 > 0.
  Comparison.ofRats ((486214 : Rat)/1000000) ((cellDelta a128)) .lt,
  -- A128.balance; A128: D=8/5, lambda in [3/2,7/4], y in [9/8,21/16], m=49/100: delta > 486214/1000000 > 0; B_balance > 90358/1000000 > 0.
  Comparison.ofRats ((90358 : Rat)/1000000) ((cellBalance a128)) .lt,
  -- A129.den; A129: D=8/5, lambda in [3/2,7/4], y in [21/16,3/2], m=49/100: delta > 442314/1000000 > 0; B_balance > 128432/1000000 > 0.
  Comparison.ofRats ((442314 : Rat)/1000000) ((cellDelta a129)) .lt,
  -- A129.balance; A129: D=8/5, lambda in [3/2,7/4], y in [21/16,3/2], m=49/100: delta > 442314/1000000 > 0; B_balance > 128432/1000000 > 0.
  Comparison.ofRats ((128432 : Rat)/1000000) ((cellBalance a129)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict075
