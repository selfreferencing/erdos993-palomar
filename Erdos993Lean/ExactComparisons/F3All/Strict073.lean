module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict073

def records : List Comparison := [
  -- A106.den; A106: D=7/5, lambda in [263/200,3/2], y in [3/8,9/16], m=2/5: delta > 766204/1000000 > 0; B_balance > 4465/1000000 > 0.
  Comparison.ofRats ((766204 : Rat)/1000000) ((cellDelta a106)) .lt,
  -- A106.balance; A106: D=7/5, lambda in [263/200,3/2], y in [3/8,9/16], m=2/5: delta > 766204/1000000 > 0; B_balance > 4465/1000000 > 0.
  Comparison.ofRats ((4465 : Rat)/1000000) ((cellBalance a106)) .lt,
  -- A107.den; A107: D=7/5, lambda in [263/200,3/2], y in [9/16,21/32], m=49/100: delta > 765155/1000000 > 0; B_balance > 33905/1000000 > 0.
  Comparison.ofRats ((765155 : Rat)/1000000) ((cellDelta a107)) .lt,
  -- A107.balance; A107: D=7/5, lambda in [263/200,3/2], y in [9/16,21/32], m=49/100: delta > 765155/1000000 > 0; B_balance > 33905/1000000 > 0.
  Comparison.ofRats ((33905 : Rat)/1000000) ((cellBalance a107)) .lt,
  -- A108.den; A108: D=7/5, lambda in [263/200,3/2], y in [21/32,3/4], m=49/100: delta > 728010/1000000 > 0; B_balance > 47067/1000000 > 0.
  Comparison.ofRats ((728010 : Rat)/1000000) ((cellDelta a108)) .lt,
  -- A108.balance; A108: D=7/5, lambda in [263/200,3/2], y in [21/32,3/4], m=49/100: delta > 728010/1000000 > 0; B_balance > 47067/1000000 > 0.
  Comparison.ofRats ((47067 : Rat)/1000000) ((cellBalance a108)) .lt,
  -- A109.den; A109: D=7/5, lambda in [263/200,3/2], y in [3/4,27/32], m=49/100: delta > 691734/1000000 > 0; B_balance > 62995/1000000 > 0.
  Comparison.ofRats ((691734 : Rat)/1000000) ((cellDelta a109)) .lt,
  -- A109.balance; A109: D=7/5, lambda in [263/200,3/2], y in [3/4,27/32], m=49/100: delta > 691734/1000000 > 0; B_balance > 62995/1000000 > 0.
  Comparison.ofRats ((62995 : Rat)/1000000) ((cellBalance a109)) .lt,
  -- A110.den; A110: D=7/5, lambda in [263/200,3/2], y in [27/32,15/16], m=49/100: delta > 656955/1000000 > 0; B_balance > 82571/1000000 > 0.
  Comparison.ofRats ((656955 : Rat)/1000000) ((cellDelta a110)) .lt,
  -- A110.balance; A110: D=7/5, lambda in [263/200,3/2], y in [27/32,15/16], m=49/100: delta > 656955/1000000 > 0; B_balance > 82571/1000000 > 0.
  Comparison.ofRats ((82571 : Rat)/1000000) ((cellBalance a110)) .lt,
  -- A111.den; A111: D=7/5, lambda in [263/200,3/2], y in [15/16,33/32], m=49/100: delta > 624356/1000000 > 0; B_balance > 106135/1000000 > 0.
  Comparison.ofRats ((624356 : Rat)/1000000) ((cellDelta a111)) .lt,
  -- A111.balance; A111: D=7/5, lambda in [263/200,3/2], y in [15/16,33/32], m=49/100: delta > 624356/1000000 > 0; B_balance > 106135/1000000 > 0.
  Comparison.ofRats ((106135 : Rat)/1000000) ((cellBalance a111)) .lt,
  -- A112.den; A112: D=7/5, lambda in [263/200,3/2], y in [33/32,9/8], m=49/100: delta > 594015/1000000 > 0; B_balance > 133466/1000000 > 0.
  Comparison.ofRats ((594015 : Rat)/1000000) ((cellDelta a112)) .lt,
  -- A112.balance; A112: D=7/5, lambda in [263/200,3/2], y in [33/32,9/8], m=49/100: delta > 594015/1000000 > 0; B_balance > 133466/1000000 > 0.
  Comparison.ofRats ((133466 : Rat)/1000000) ((cellBalance a112)) .lt,
  -- A113.den; A113: D=7/5, lambda in [263/200,3/2], y in [9/8,39/32], m=49/100: delta > 566344/1000000 > 0; B_balance > 165026/1000000 > 0.
  Comparison.ofRats ((566344 : Rat)/1000000) ((cellDelta a113)) .lt,
  -- A113.balance; A113: D=7/5, lambda in [263/200,3/2], y in [9/8,39/32], m=49/100: delta > 566344/1000000 > 0; B_balance > 165026/1000000 > 0.
  Comparison.ofRats ((165026 : Rat)/1000000) ((cellBalance a113)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict073
