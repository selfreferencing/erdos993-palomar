module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict074

def records : List Comparison := [
  -- A114.den; A114: D=7/5, lambda in [263/200,3/2], y in [39/32,21/16], m=49/100: delta > 542959/1000000 > 0; B_balance > 205461/1000000 > 0.
  Comparison.ofRats ((542959 : Rat)/1000000) ((cellDelta a114)) .lt,
  -- A114.balance; A114: D=7/5, lambda in [263/200,3/2], y in [39/32,21/16], m=49/100: delta > 542959/1000000 > 0; B_balance > 205461/1000000 > 0.
  Comparison.ofRats ((205461 : Rat)/1000000) ((cellBalance a114)) .lt,
  -- A115.den; A115: D=7/5, lambda in [263/200,3/2], y in [21/16,45/32], m=49/100: delta > 524786/1000000 > 0; B_balance > 259771/1000000 > 0.
  Comparison.ofRats ((524786 : Rat)/1000000) ((cellDelta a115)) .lt,
  -- A115.balance; A115: D=7/5, lambda in [263/200,3/2], y in [21/16,45/32], m=49/100: delta > 524786/1000000 > 0; B_balance > 259771/1000000 > 0.
  Comparison.ofRats ((259771 : Rat)/1000000) ((cellBalance a115)) .lt,
  -- A116.den; A116: D=7/5, lambda in [263/200,3/2], y in [45/32,3/2], m=49/100: delta > 512819/1000000 > 0; B_balance > 335286/1000000 > 0.
  Comparison.ofRats ((512819 : Rat)/1000000) ((cellDelta a116)) .lt,
  -- A116.balance; A116: D=7/5, lambda in [263/200,3/2], y in [45/32,3/2], m=49/100: delta > 512819/1000000 > 0; B_balance > 335286/1000000 > 0.
  Comparison.ofRats ((335286 : Rat)/1000000) ((cellBalance a116)) .lt,
  -- A117.den; A117: D=7/5, lambda in [263/200,3/2], y in [3/2,27/16], m=49/100: delta > 399708/1000000 > 0; B_balance > 50669/1000000 > 0.
  Comparison.ofRats ((399708 : Rat)/1000000) ((cellDelta a117)) .lt,
  -- A117.balance; A117: D=7/5, lambda in [263/200,3/2], y in [3/2,27/16], m=49/100: delta > 399708/1000000 > 0; B_balance > 50669/1000000 > 0.
  Comparison.ofRats ((50669 : Rat)/1000000) ((cellBalance a117)) .lt,
  -- A118.den; A118: D=7/5, lambda in [263/200,3/2], y in [27/16,15/8], m=49/100: delta > 414145/1000000 > 0; B_balance > 340900/1000000 > 0.
  Comparison.ofRats ((414145 : Rat)/1000000) ((cellDelta a118)) .lt,
  -- A118.balance; A118: D=7/5, lambda in [263/200,3/2], y in [27/16,15/8], m=49/100: delta > 414145/1000000 > 0; B_balance > 340900/1000000 > 0.
  Comparison.ofRats ((340900 : Rat)/1000000) ((cellBalance a118)) .lt,
  -- A119.den; A119: D=7/5, lambda in [263/200,3/2], y in [15/8,33/16], m=49/100: delta > 473150/1000000 > 0; B_balance > 978955/1000000 > 0.
  Comparison.ofRats ((473150 : Rat)/1000000) ((cellDelta a119)) .lt,
  -- A119.balance; A119: D=7/5, lambda in [263/200,3/2], y in [15/8,33/16], m=49/100: delta > 473150/1000000 > 0; B_balance > 978955/1000000 > 0.
  Comparison.ofRats ((978955 : Rat)/1000000) ((cellBalance a119)) .lt,
  -- A120.den; A120: D=7/5, lambda in [263/200,3/2], y in [33/16,9/4], m=49/100: delta > 588170/1000000 > 0; B_balance > 2024459/1000000 > 0.
  Comparison.ofRats ((588170 : Rat)/1000000) ((cellDelta a120)) .lt,
  -- A120.balance; A120: D=7/5, lambda in [263/200,3/2], y in [33/16,9/4], m=49/100: delta > 588170/1000000 > 0; B_balance > 2024459/1000000 > 0.
  Comparison.ofRats ((2024459 : Rat)/1000000) ((cellBalance a120)) .lt,
  -- A121.den; A121: D=7/5, lambda in [263/200,3/2], y in [9/4,21/8], m=49/100: delta > 543517/1000000 > 0; B_balance > 2553388/1000000 > 0.
  Comparison.ofRats ((543517 : Rat)/1000000) ((cellDelta a121)) .lt,
  -- A121.balance; A121: D=7/5, lambda in [263/200,3/2], y in [9/4,21/8], m=49/100: delta > 543517/1000000 > 0; B_balance > 2553388/1000000 > 0.
  Comparison.ofRats ((2553388 : Rat)/1000000) ((cellBalance a121)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict074
