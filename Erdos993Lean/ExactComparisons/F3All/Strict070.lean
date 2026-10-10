module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict070

def records : List Comparison := [
  -- A082.den; A082: D=6/5, lambda in [28/25,263/200], y in [57/64,15/16], m=49/100: delta > 642926/1000000 > 0; B_balance > 180/1000000 > 0.
  Comparison.ofRats ((642926 : Rat)/1000000) ((cellDelta a082)) .lt,
  -- A082.balance; A082: D=6/5, lambda in [28/25,263/200], y in [57/64,15/16], m=49/100: delta > 642926/1000000 > 0; B_balance > 180/1000000 > 0.
  Comparison.ofRats ((180 : Rat)/1000000) ((cellBalance a082)) .lt,
  -- A083.den; A083: D=6/5, lambda in [28/25,263/200], y in [15/16,63/64], m=49/100: delta > 624679/1000000 > 0; B_balance > 2458/1000000 > 0.
  Comparison.ofRats ((624679 : Rat)/1000000) ((cellDelta a083)) .lt,
  -- A083.balance; A083: D=6/5, lambda in [28/25,263/200], y in [15/16,63/64], m=49/100: delta > 624679/1000000 > 0; B_balance > 2458/1000000 > 0.
  Comparison.ofRats ((2458 : Rat)/1000000) ((cellBalance a083)) .lt,
  -- A084.den; A084: D=6/5, lambda in [28/25,263/200], y in [63/64,33/32], m=49/100: delta > 607196/1000000 > 0; B_balance > 5226/1000000 > 0.
  Comparison.ofRats ((607196 : Rat)/1000000) ((cellDelta a084)) .lt,
  -- A084.balance; A084: D=6/5, lambda in [28/25,263/200], y in [63/64,33/32], m=49/100: delta > 607196/1000000 > 0; B_balance > 5226/1000000 > 0.
  Comparison.ofRats ((5226 : Rat)/1000000) ((cellBalance a084)) .lt,
  -- A085.den; A085: D=6/5, lambda in [28/25,263/200], y in [33/32,69/64], m=49/100: delta > 590581/1000000 > 0; B_balance > 8736/1000000 > 0.
  Comparison.ofRats ((590581 : Rat)/1000000) ((cellDelta a085)) .lt,
  -- A085.balance; A085: D=6/5, lambda in [28/25,263/200], y in [33/32,69/64], m=49/100: delta > 590581/1000000 > 0; B_balance > 8736/1000000 > 0.
  Comparison.ofRats ((8736 : Rat)/1000000) ((cellBalance a085)) .lt,
  -- A086.den; A086: D=6/5, lambda in [28/25,263/200], y in [69/64,9/8], m=49/100: delta > 574942/1000000 > 0; B_balance > 13342/1000000 > 0.
  Comparison.ofRats ((574942 : Rat)/1000000) ((cellDelta a086)) .lt,
  -- A086.balance; A086: D=6/5, lambda in [28/25,263/200], y in [69/64,9/8], m=49/100: delta > 574942/1000000 > 0; B_balance > 13342/1000000 > 0.
  Comparison.ofRats ((13342 : Rat)/1000000) ((cellBalance a086)) .lt,
  -- A087.den; A087: D=6/5, lambda in [28/25,263/200], y in [9/8,75/64], m=49/100: delta > 560391/1000000 > 0; B_balance > 19524/1000000 > 0.
  Comparison.ofRats ((560391 : Rat)/1000000) ((cellDelta a087)) .lt,
  -- A087.balance; A087: D=6/5, lambda in [28/25,263/200], y in [9/8,75/64], m=49/100: delta > 560391/1000000 > 0; B_balance > 19524/1000000 > 0.
  Comparison.ofRats ((19524 : Rat)/1000000) ((cellBalance a087)) .lt,
  -- A088.den; A088: D=6/5, lambda in [28/25,263/200], y in [75/64,39/32], m=49/100: delta > 547042/1000000 > 0; B_balance > 27918/1000000 > 0.
  Comparison.ofRats ((547042 : Rat)/1000000) ((cellDelta a088)) .lt,
  -- A088.balance; A088: D=6/5, lambda in [28/25,263/200], y in [75/64,39/32], m=49/100: delta > 547042/1000000 > 0; B_balance > 27918/1000000 > 0.
  Comparison.ofRats ((27918 : Rat)/1000000) ((cellBalance a088)) .lt,
  -- A089.den; A089: D=6/5, lambda in [28/25,263/200], y in [39/32,81/64], m=49/100: delta > 534056/1000000 > 0; B_balance > 35070/1000000 > 0.
  Comparison.ofRats ((534056 : Rat)/1000000) ((cellDelta a089)) .lt,
  -- A089.balance; A089: D=6/5, lambda in [28/25,263/200], y in [39/32,81/64], m=49/100: delta > 534056/1000000 > 0; B_balance > 35070/1000000 > 0.
  Comparison.ofRats ((35070 : Rat)/1000000) ((cellBalance a089)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict070
