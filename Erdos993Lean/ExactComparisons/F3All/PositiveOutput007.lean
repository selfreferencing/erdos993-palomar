module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput007

def records : List Comparison := [
  -- A158.positive_gp; A158: D=21/10, lambda in [2,7/3], y in [9/4,21/8], m=49/100: delta > 473844/1000000 > 0; B_balance > 1458080/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((473844 : Rat)) .lt,
  -- A158.positive_g; A158: D=21/10, lambda in [2,7/3], y in [9/4,21/8], m=49/100: delta > 473844/1000000 > 0; B_balance > 1458080/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1458080 : Rat)) .lt,
  -- A159.positive_gp; A159: D=21/10, lambda in [2,7/3], y in [21/8,3], m=49/100: delta > 982834/1000000 > 0; B_balance > 4021938/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((982834 : Rat)) .lt,
  -- A159.positive_g; A159: D=21/10, lambda in [2,7/3], y in [21/8,3], m=49/100: delta > 982834/1000000 > 0; B_balance > 4021938/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4021938 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 4 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput007
