module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict072

def records : List Comparison := [
  -- A098.den; A098: D=6/5, lambda in [28/25,263/200], y in [27/16,57/32], m=49/100: delta > 440072/1000000 > 0; B_balance > 193971/1000000 > 0.
  Comparison.ofRats ((440072 : Rat)/1000000) ((cellDelta a098)) .lt,
  -- A098.balance; A098: D=6/5, lambda in [28/25,263/200], y in [27/16,57/32], m=49/100: delta > 440072/1000000 > 0; B_balance > 193971/1000000 > 0.
  Comparison.ofRats ((193971 : Rat)/1000000) ((cellBalance a098)) .lt,
  -- A099.den; A099: D=6/5, lambda in [28/25,263/200], y in [57/32,15/8], m=49/100: delta > 461680/1000000 > 0; B_balance > 491647/1000000 > 0.
  Comparison.ofRats ((461680 : Rat)/1000000) ((cellDelta a099)) .lt,
  -- A099.balance; A099: D=6/5, lambda in [28/25,263/200], y in [57/32,15/8], m=49/100: delta > 461680/1000000 > 0; B_balance > 491647/1000000 > 0.
  Comparison.ofRats ((491647 : Rat)/1000000) ((cellBalance a099)) .lt,
  -- A100.den; A100: D=6/5, lambda in [28/25,263/200], y in [15/8,63/32], m=49/100: delta > 496256/1000000 > 0; B_balance > 912229/1000000 > 0.
  Comparison.ofRats ((496256 : Rat)/1000000) ((cellDelta a100)) .lt,
  -- A100.balance; A100: D=6/5, lambda in [28/25,263/200], y in [15/8,63/32], m=49/100: delta > 496256/1000000 > 0; B_balance > 912229/1000000 > 0.
  Comparison.ofRats ((912229 : Rat)/1000000) ((cellBalance a100)) .lt,
  -- A101.den; A101: D=6/5, lambda in [28/25,263/200], y in [63/32,33/16], m=49/100: delta > 545355/1000000 > 0; B_balance > 1462111/1000000 > 0.
  Comparison.ofRats ((545355 : Rat)/1000000) ((cellDelta a101)) .lt,
  -- A101.balance; A101: D=6/5, lambda in [28/25,263/200], y in [63/32,33/16], m=49/100: delta > 545355/1000000 > 0; B_balance > 1462111/1000000 > 0.
  Comparison.ofRats ((1462111 : Rat)/1000000) ((cellBalance a101)) .lt,
  -- A102.den; A102: D=6/5, lambda in [28/25,263/200], y in [33/16,9/4], m=49/100: delta > 488316/1000000 > 0; B_balance > 1389088/1000000 > 0.
  Comparison.ofRats ((488316 : Rat)/1000000) ((cellDelta a102)) .lt,
  -- A102.balance; A102: D=6/5, lambda in [28/25,263/200], y in [33/16,9/4], m=49/100: delta > 488316/1000000 > 0; B_balance > 1389088/1000000 > 0.
  Comparison.ofRats ((1389088 : Rat)/1000000) ((cellBalance a102)) .lt,
  -- A103.den; A103: D=6/5, lambda in [28/25,263/200], y in [9/4,21/8], m=49/100: delta > 428874/1000000 > 0; B_balance > 1438246/1000000 > 0.
  Comparison.ofRats ((428874 : Rat)/1000000) ((cellDelta a103)) .lt,
  -- A103.balance; A103: D=6/5, lambda in [28/25,263/200], y in [9/4,21/8], m=49/100: delta > 428874/1000000 > 0; B_balance > 1438246/1000000 > 0.
  Comparison.ofRats ((1438246 : Rat)/1000000) ((cellBalance a103)) .lt,
  -- A104.den; A104: D=6/5, lambda in [28/25,263/200], y in [21/8,3], m=49/100: delta > 1087949/1000000 > 0; B_balance > 8016025/1000000 > 0.
  Comparison.ofRats ((1087949 : Rat)/1000000) ((cellDelta a104)) .lt,
  -- A104.balance; A104: D=6/5, lambda in [28/25,263/200], y in [21/8,3], m=49/100: delta > 1087949/1000000 > 0; B_balance > 8016025/1000000 > 0.
  Comparison.ofRats ((8016025 : Rat)/1000000) ((cellBalance a104)) .lt,
  -- A105.den; A105: D=7/5, lambda in [263/200,3/2], y in [0,3/8], m=1/3: delta > 793753/1000000 > 0; B_balance > 96522/1000000 > 0.
  Comparison.ofRats ((793753 : Rat)/1000000) ((cellDelta a105)) .lt,
  -- A105.balance; A105: D=7/5, lambda in [263/200,3/2], y in [0,3/8], m=1/3: delta > 793753/1000000 > 0; B_balance > 96522/1000000 > 0.
  Comparison.ofRats ((96522 : Rat)/1000000) ((cellBalance a105)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict072
