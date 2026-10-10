module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict064

def records : List Comparison := [
  -- A034.den; A034: D=6/5, lambda in [7/8,28/25], y in [0,3/16], m=0: delta > 945668/1000000 > 0; B_balance > 207139/1000000 > 0.
  Comparison.ofRats ((945668 : Rat)/1000000) ((cellDelta a034)) .lt,
  -- A034.balance; A034: D=6/5, lambda in [7/8,28/25], y in [0,3/16], m=0: delta > 945668/1000000 > 0; B_balance > 207139/1000000 > 0.
  Comparison.ofRats ((207139 : Rat)/1000000) ((cellBalance a034)) .lt,
  -- A035.den; A035: D=6/5, lambda in [7/8,28/25], y in [3/16,9/32], m=1/3: delta > 932470/1000000 > 0; B_balance > 97185/1000000 > 0.
  Comparison.ofRats ((932470 : Rat)/1000000) ((cellDelta a035)) .lt,
  -- A035.balance; A035: D=6/5, lambda in [7/8,28/25], y in [3/16,9/32], m=1/3: delta > 932470/1000000 > 0; B_balance > 97185/1000000 > 0.
  Comparison.ofRats ((97185 : Rat)/1000000) ((cellBalance a035)) .lt,
  -- A036.den; A036: D=6/5, lambda in [7/8,28/25], y in [9/32,3/8], m=1/3: delta > 890731/1000000 > 0; B_balance > 16977/1000000 > 0.
  Comparison.ofRats ((890731 : Rat)/1000000) ((cellDelta a036)) .lt,
  -- A036.balance; A036: D=6/5, lambda in [7/8,28/25], y in [9/32,3/8], m=1/3: delta > 890731/1000000 > 0; B_balance > 16977/1000000 > 0.
  Comparison.ofRats ((16977 : Rat)/1000000) ((cellBalance a036)) .lt,
  -- A037.den; A037: D=6/5, lambda in [7/8,28/25], y in [3/8,27/64], m=2/5: delta > 888230/1000000 > 0; B_balance > 7288/1000000 > 0.
  Comparison.ofRats ((888230 : Rat)/1000000) ((cellDelta a037)) .lt,
  -- A037.balance; A037: D=6/5, lambda in [7/8,28/25], y in [3/8,27/64], m=2/5: delta > 888230/1000000 > 0; B_balance > 7288/1000000 > 0.
  Comparison.ofRats ((7288 : Rat)/1000000) ((cellBalance a037)) .lt,
  -- A038.den; A038: D=6/5, lambda in [7/8,28/25], y in [27/64,15/32], m=49/100: delta > 867907/1000000 > 0; B_balance > 1263/1000000 > 0.
  Comparison.ofRats ((867907 : Rat)/1000000) ((cellDelta a038)) .lt,
  -- A038.balance; A038: D=6/5, lambda in [7/8,28/25], y in [27/64,15/32], m=49/100: delta > 867907/1000000 > 0; B_balance > 1263/1000000 > 0.
  Comparison.ofRats ((1263 : Rat)/1000000) ((cellBalance a038)) .lt,
  -- A039.den; A039: D=6/5, lambda in [7/8,28/25], y in [15/32,33/64], m=49/100: delta > 847603/1000000 > 0; B_balance > 4559/1000000 > 0.
  Comparison.ofRats ((847603 : Rat)/1000000) ((cellDelta a039)) .lt,
  -- A039.balance; A039: D=6/5, lambda in [7/8,28/25], y in [15/32,33/64], m=49/100: delta > 847603/1000000 > 0; B_balance > 4559/1000000 > 0.
  Comparison.ofRats ((4559 : Rat)/1000000) ((cellBalance a039)) .lt,
  -- A040.den; A040: D=6/5, lambda in [7/8,28/25], y in [33/64,9/16], m=49/100: delta > 827390/1000000 > 0; B_balance > 8695/1000000 > 0.
  Comparison.ofRats ((827390 : Rat)/1000000) ((cellDelta a040)) .lt,
  -- A040.balance; A040: D=6/5, lambda in [7/8,28/25], y in [33/64,9/16], m=49/100: delta > 827390/1000000 > 0; B_balance > 8695/1000000 > 0.
  Comparison.ofRats ((8695 : Rat)/1000000) ((cellBalance a040)) .lt,
  -- A041.den; A041: D=6/5, lambda in [7/8,28/25], y in [9/16,39/64], m=49/100: delta > 807340/1000000 > 0; B_balance > 13723/1000000 > 0.
  Comparison.ofRats ((807340 : Rat)/1000000) ((cellDelta a041)) .lt,
  -- A041.balance; A041: D=6/5, lambda in [7/8,28/25], y in [9/16,39/64], m=49/100: delta > 807340/1000000 > 0; B_balance > 13723/1000000 > 0.
  Comparison.ofRats ((13723 : Rat)/1000000) ((cellBalance a041)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict064
