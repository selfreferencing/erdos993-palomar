module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict079

def records : List Comparison := [
  -- A154.den; A154: D=21/10, lambda in [2,7/3], y in [3/2,27/16], m=49/100: delta > 419493/1000000 > 0; B_balance > 284530/1000000 > 0.
  Comparison.ofRats ((419493 : Rat)/1000000) ((cellDelta a154)) .lt,
  -- A154.balance; A154: D=21/10, lambda in [2,7/3], y in [3/2,27/16], m=49/100: delta > 419493/1000000 > 0; B_balance > 284530/1000000 > 0.
  Comparison.ofRats ((284530 : Rat)/1000000) ((cellBalance a154)) .lt,
  -- A155.den; A155: D=21/10, lambda in [2,7/3], y in [27/16,15/8], m=49/100: delta > 421680/1000000 > 0; B_balance > 444171/1000000 > 0.
  Comparison.ofRats ((421680 : Rat)/1000000) ((cellDelta a155)) .lt,
  -- A155.balance; A155: D=21/10, lambda in [2,7/3], y in [27/16,15/8], m=49/100: delta > 421680/1000000 > 0; B_balance > 444171/1000000 > 0.
  Comparison.ofRats ((444171 : Rat)/1000000) ((cellBalance a155)) .lt,
  -- A156.den; A156: D=21/10, lambda in [2,7/3], y in [15/8,33/16], m=49/100: delta > 459434/1000000 > 0; B_balance > 748301/1000000 > 0.
  Comparison.ofRats ((459434 : Rat)/1000000) ((cellDelta a156)) .lt,
  -- A156.balance; A156: D=21/10, lambda in [2,7/3], y in [15/8,33/16], m=49/100: delta > 459434/1000000 > 0; B_balance > 748301/1000000 > 0.
  Comparison.ofRats ((748301 : Rat)/1000000) ((cellBalance a156)) .lt,
  -- A157.den; A157: D=21/10, lambda in [2,7/3], y in [33/16,9/4], m=49/100: delta > 542783/1000000 > 0; B_balance > 1256418/1000000 > 0.
  Comparison.ofRats ((542783 : Rat)/1000000) ((cellDelta a157)) .lt,
  -- A157.balance; A157: D=21/10, lambda in [2,7/3], y in [33/16,9/4], m=49/100: delta > 542783/1000000 > 0; B_balance > 1256418/1000000 > 0.
  Comparison.ofRats ((1256418 : Rat)/1000000) ((cellBalance a157)) .lt,
  -- A158.den; A158: D=21/10, lambda in [2,7/3], y in [9/4,21/8], m=49/100: delta > 473844/1000000 > 0; B_balance > 1458080/1000000 > 0.
  Comparison.ofRats ((473844 : Rat)/1000000) ((cellDelta a158)) .lt,
  -- A158.balance; A158: D=21/10, lambda in [2,7/3], y in [9/4,21/8], m=49/100: delta > 473844/1000000 > 0; B_balance > 1458080/1000000 > 0.
  Comparison.ofRats ((1458080 : Rat)/1000000) ((cellBalance a158)) .lt,
  -- A159.den; A159: D=21/10, lambda in [2,7/3], y in [21/8,3], m=49/100: delta > 982834/1000000 > 0; B_balance > 4021938/1000000 > 0.
  Comparison.ofRats ((982834 : Rat)/1000000) ((cellDelta a159)) .lt,
  -- A159.balance; A159: D=21/10, lambda in [2,7/3], y in [21/8,3], m=49/100: delta > 982834/1000000 > 0; B_balance > 4021938/1000000 > 0.
  Comparison.ofRats ((4021938 : Rat)/1000000) ((cellBalance a159)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 12 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict079
