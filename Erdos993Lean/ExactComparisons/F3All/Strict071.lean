module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict071

def records : List Comparison := [
  -- A090.den; A090: D=6/5, lambda in [28/25,263/200], y in [81/64,21/16], m=49/100: delta > 522235/1000000 > 0; B_balance > 44319/1000000 > 0.
  Comparison.ofRats ((522235 : Rat)/1000000) ((cellDelta a090)) .lt,
  -- A090.balance; A090: D=6/5, lambda in [28/25,263/200], y in [81/64,21/16], m=49/100: delta > 522235/1000000 > 0; B_balance > 44319/1000000 > 0.
  Comparison.ofRats ((44319 : Rat)/1000000) ((cellBalance a090)) .lt,
  -- A091.den; A091: D=6/5, lambda in [28/25,263/200], y in [21/16,87/64], m=49/100: delta > 511897/1000000 > 0; B_balance > 57594/1000000 > 0.
  Comparison.ofRats ((511897 : Rat)/1000000) ((cellDelta a091)) .lt,
  -- A091.balance; A091: D=6/5, lambda in [28/25,263/200], y in [21/16,87/64], m=49/100: delta > 511897/1000000 > 0; B_balance > 57594/1000000 > 0.
  Comparison.ofRats ((57594 : Rat)/1000000) ((cellBalance a091)) .lt,
  -- A092.den; A092: D=6/5, lambda in [28/25,263/200], y in [87/64,45/32], m=49/100: delta > 503176/1000000 > 0; B_balance > 76301/1000000 > 0.
  Comparison.ofRats ((503176 : Rat)/1000000) ((cellDelta a092)) .lt,
  -- A092.balance; A092: D=6/5, lambda in [28/25,263/200], y in [87/64,45/32], m=49/100: delta > 503176/1000000 > 0; B_balance > 76301/1000000 > 0.
  Comparison.ofRats ((76301 : Rat)/1000000) ((cellBalance a092)) .lt,
  -- A093.den; A093: D=6/5, lambda in [28/25,263/200], y in [45/32,93/64], m=49/100: delta > 496208/1000000 > 0; B_balance > 102115/1000000 > 0.
  Comparison.ofRats ((496208 : Rat)/1000000) ((cellDelta a093)) .lt,
  -- A093.balance; A093: D=6/5, lambda in [28/25,263/200], y in [45/32,93/64], m=49/100: delta > 496208/1000000 > 0; B_balance > 102115/1000000 > 0.
  Comparison.ofRats ((102115 : Rat)/1000000) ((cellBalance a093)) .lt,
  -- A094.den; A094: D=6/5, lambda in [28/25,263/200], y in [93/64,3/2], m=49/100: delta > 491137/1000000 > 0; B_balance > 136972/1000000 > 0.
  Comparison.ofRats ((491137 : Rat)/1000000) ((cellDelta a094)) .lt,
  -- A094.balance; A094: D=6/5, lambda in [28/25,263/200], y in [93/64,3/2], m=49/100: delta > 491137/1000000 > 0; B_balance > 136972/1000000 > 0.
  Comparison.ofRats ((136972 : Rat)/1000000) ((cellBalance a094)) .lt,
  -- A095.den; A095: D=6/5, lambda in [28/25,263/200], y in [3/2,99/64], m=49/100: delta > 488107/1000000 > 0; B_balance > 183050/1000000 > 0.
  Comparison.ofRats ((488107 : Rat)/1000000) ((cellDelta a095)) .lt,
  -- A095.balance; A095: D=6/5, lambda in [28/25,263/200], y in [3/2,99/64], m=49/100: delta > 488107/1000000 > 0; B_balance > 183050/1000000 > 0.
  Comparison.ofRats ((183050 : Rat)/1000000) ((cellBalance a095)) .lt,
  -- A096.den; A096: D=6/5, lambda in [28/25,263/200], y in [99/64,51/32], m=49/100: delta > 487272/1000000 > 0; B_balance > 242707/1000000 > 0.
  Comparison.ofRats ((487272 : Rat)/1000000) ((cellDelta a096)) .lt,
  -- A096.balance; A096: D=6/5, lambda in [28/25,263/200], y in [99/64,51/32], m=49/100: delta > 487272/1000000 > 0; B_balance > 242707/1000000 > 0.
  Comparison.ofRats ((242707 : Rat)/1000000) ((cellBalance a096)) .lt,
  -- A097.den; A097: D=6/5, lambda in [28/25,263/200], y in [51/32,27/16], m=49/100: delta > 429985/1000000 > 0; B_balance > 4245/1000000 > 0.
  Comparison.ofRats ((429985 : Rat)/1000000) ((cellDelta a097)) .lt,
  -- A097.balance; A097: D=6/5, lambda in [28/25,263/200], y in [51/32,27/16], m=49/100: delta > 429985/1000000 > 0; B_balance > 4245/1000000 > 0.
  Comparison.ofRats ((4245 : Rat)/1000000) ((cellBalance a097)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict071
