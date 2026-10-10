module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict060

def records : List Comparison := [
  -- A002.den; A002: D=6/5, lambda in [1/3,3/5], y in [3/32,3/16], m=1/3: delta > 1033475/1000000 > 0; B_balance > 9028/1000000 > 0.
  Comparison.ofRats ((1033475 : Rat)/1000000) ((cellDelta a002)) .lt,
  -- A002.balance; A002: D=6/5, lambda in [1/3,3/5], y in [3/32,3/16], m=1/3: delta > 1033475/1000000 > 0; B_balance > 9028/1000000 > 0.
  Comparison.ofRats ((9028 : Rat)/1000000) ((cellBalance a002)) .lt,
  -- A003.den; A003: D=6/5, lambda in [1/3,3/5], y in [3/16,15/64], m=49/100: delta > 1031270/1000000 > 0; B_balance > 13252/1000000 > 0.
  Comparison.ofRats ((1031270 : Rat)/1000000) ((cellDelta a003)) .lt,
  -- A003.balance; A003: D=6/5, lambda in [1/3,3/5], y in [3/16,15/64], m=49/100: delta > 1031270/1000000 > 0; B_balance > 13252/1000000 > 0.
  Comparison.ofRats ((13252 : Rat)/1000000) ((cellBalance a003)) .lt,
  -- A004.den; A004: D=6/5, lambda in [1/3,3/5], y in [15/64,9/32], m=49/100: delta > 1012119/1000000 > 0; B_balance > 23985/1000000 > 0.
  Comparison.ofRats ((1012119 : Rat)/1000000) ((cellDelta a004)) .lt,
  -- A004.balance; A004: D=6/5, lambda in [1/3,3/5], y in [15/64,9/32], m=49/100: delta > 1012119/1000000 > 0; B_balance > 23985/1000000 > 0.
  Comparison.ofRats ((23985 : Rat)/1000000) ((cellBalance a004)) .lt,
  -- A005.den; A005: D=6/5, lambda in [1/3,3/5], y in [9/32,3/8], m=49/100: delta > 954116/1000000 > 0; B_balance > 10608/1000000 > 0.
  Comparison.ofRats ((954116 : Rat)/1000000) ((cellDelta a005)) .lt,
  -- A005.balance; A005: D=6/5, lambda in [1/3,3/5], y in [9/32,3/8], m=49/100: delta > 954116/1000000 > 0; B_balance > 10608/1000000 > 0.
  Comparison.ofRats ((10608 : Rat)/1000000) ((cellBalance a005)) .lt,
  -- A006.den; A006: D=6/5, lambda in [1/3,3/5], y in [3/8,15/32], m=49/100: delta > 916701/1000000 > 0; B_balance > 43795/1000000 > 0.
  Comparison.ofRats ((916701 : Rat)/1000000) ((cellDelta a006)) .lt,
  -- A006.balance; A006: D=6/5, lambda in [1/3,3/5], y in [3/8,15/32], m=49/100: delta > 916701/1000000 > 0; B_balance > 43795/1000000 > 0.
  Comparison.ofRats ((43795 : Rat)/1000000) ((cellBalance a006)) .lt,
  -- A007.den; A007: D=6/5, lambda in [1/3,3/5], y in [15/32,9/16], m=49/100: delta > 881557/1000000 > 0; B_balance > 91807/1000000 > 0.
  Comparison.ofRats ((881557 : Rat)/1000000) ((cellDelta a007)) .lt,
  -- A007.balance; A007: D=6/5, lambda in [1/3,3/5], y in [15/32,9/16], m=49/100: delta > 881557/1000000 > 0; B_balance > 91807/1000000 > 0.
  Comparison.ofRats ((91807 : Rat)/1000000) ((cellBalance a007)) .lt,
  -- A008.den; A008: D=6/5, lambda in [1/3,3/5], y in [9/16,3/4], m=49/100: delta > 764244/1000000 > 0; B_balance > 34482/1000000 > 0.
  Comparison.ofRats ((764244 : Rat)/1000000) ((cellDelta a008)) .lt,
  -- A008.balance; A008: D=6/5, lambda in [1/3,3/5], y in [9/16,3/4], m=49/100: delta > 764244/1000000 > 0; B_balance > 34482/1000000 > 0.
  Comparison.ofRats ((34482 : Rat)/1000000) ((cellBalance a008)) .lt,
  -- A009.den; A009: D=6/5, lambda in [1/3,3/5], y in [3/4,15/16], m=49/100: delta > 707087/1000000 > 0; B_balance > 186431/1000000 > 0.
  Comparison.ofRats ((707087 : Rat)/1000000) ((cellDelta a009)) .lt,
  -- A009.balance; A009: D=6/5, lambda in [1/3,3/5], y in [3/4,15/16], m=49/100: delta > 707087/1000000 > 0; B_balance > 186431/1000000 > 0.
  Comparison.ofRats ((186431 : Rat)/1000000) ((cellBalance a009)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict060
