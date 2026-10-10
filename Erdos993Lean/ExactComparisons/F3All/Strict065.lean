module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict065

def records : List Comparison := [
  -- A042.den; A042: D=6/5, lambda in [7/8,28/25], y in [39/64,21/32], m=49/100: delta > 787532/1000000 > 0; B_balance > 20021/1000000 > 0.
  Comparison.ofRats ((787532 : Rat)/1000000) ((cellDelta a042)) .lt,
  -- A042.balance; A042: D=6/5, lambda in [7/8,28/25], y in [39/64,21/32], m=49/100: delta > 787532/1000000 > 0; B_balance > 20021/1000000 > 0.
  Comparison.ofRats ((20021 : Rat)/1000000) ((cellBalance a042)) .lt,
  -- A043.den; A043: D=6/5, lambda in [7/8,28/25], y in [21/32,45/64], m=49/100: delta > 768046/1000000 > 0; B_balance > 27576/1000000 > 0.
  Comparison.ofRats ((768046 : Rat)/1000000) ((cellDelta a043)) .lt,
  -- A043.balance; A043: D=6/5, lambda in [7/8,28/25], y in [21/32,45/64], m=49/100: delta > 768046/1000000 > 0; B_balance > 27576/1000000 > 0.
  Comparison.ofRats ((27576 : Rat)/1000000) ((cellBalance a043)) .lt,
  -- A044.den; A044: D=6/5, lambda in [7/8,28/25], y in [45/64,3/4], m=49/100: delta > 748967/1000000 > 0; B_balance > 36275/1000000 > 0.
  Comparison.ofRats ((748967 : Rat)/1000000) ((cellDelta a044)) .lt,
  -- A044.balance; A044: D=6/5, lambda in [7/8,28/25], y in [45/64,3/4], m=49/100: delta > 748967/1000000 > 0; B_balance > 36275/1000000 > 0.
  Comparison.ofRats ((36275 : Rat)/1000000) ((cellBalance a044)) .lt,
  -- A045.den; A045: D=6/5, lambda in [7/8,28/25], y in [3/4,51/64], m=49/100: delta > 730381/1000000 > 0; B_balance > 46255/1000000 > 0.
  Comparison.ofRats ((730381 : Rat)/1000000) ((cellDelta a045)) .lt,
  -- A045.balance; A045: D=6/5, lambda in [7/8,28/25], y in [3/4,51/64], m=49/100: delta > 730381/1000000 > 0; B_balance > 46255/1000000 > 0.
  Comparison.ofRats ((46255 : Rat)/1000000) ((cellBalance a045)) .lt,
  -- A046.den; A046: D=6/5, lambda in [7/8,28/25], y in [51/64,27/32], m=49/100: delta > 712378/1000000 > 0; B_balance > 57685/1000000 > 0.
  Comparison.ofRats ((712378 : Rat)/1000000) ((cellDelta a046)) .lt,
  -- A046.balance; A046: D=6/5, lambda in [7/8,28/25], y in [51/64,27/32], m=49/100: delta > 712378/1000000 > 0; B_balance > 57685/1000000 > 0.
  Comparison.ofRats ((57685 : Rat)/1000000) ((cellBalance a046)) .lt,
  -- A047.den; A047: D=6/5, lambda in [7/8,28/25], y in [27/32,15/16], m=49/100: delta > 647307/1000000 > 0; B_balance > 6605/1000000 > 0.
  Comparison.ofRats ((647307 : Rat)/1000000) ((cellDelta a047)) .lt,
  -- A047.balance; A047: D=6/5, lambda in [7/8,28/25], y in [27/32,15/16], m=49/100: delta > 647307/1000000 > 0; B_balance > 6605/1000000 > 0.
  Comparison.ofRats ((6605 : Rat)/1000000) ((cellBalance a047)) .lt,
  -- A048.den; A048: D=6/5, lambda in [7/8,28/25], y in [15/16,33/32], m=49/100: delta > 613854/1000000 > 0; B_balance > 23088/1000000 > 0.
  Comparison.ofRats ((613854 : Rat)/1000000) ((cellDelta a048)) .lt,
  -- A048.balance; A048: D=6/5, lambda in [7/8,28/25], y in [15/16,33/32], m=49/100: delta > 613854/1000000 > 0; B_balance > 23088/1000000 > 0.
  Comparison.ofRats ((23088 : Rat)/1000000) ((cellBalance a048)) .lt,
  -- A049.den; A049: D=6/5, lambda in [7/8,28/25], y in [33/32,9/8], m=49/100: delta > 584429/1000000 > 0; B_balance > 47842/1000000 > 0.
  Comparison.ofRats ((584429 : Rat)/1000000) ((cellDelta a049)) .lt,
  -- A049.balance; A049: D=6/5, lambda in [7/8,28/25], y in [33/32,9/8], m=49/100: delta > 584429/1000000 > 0; B_balance > 47842/1000000 > 0.
  Comparison.ofRats ((47842 : Rat)/1000000) ((cellBalance a049)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict065
