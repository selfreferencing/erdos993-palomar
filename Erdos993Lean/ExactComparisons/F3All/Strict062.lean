module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict062

def records : List Comparison := [
  -- A018.den; A018: D=6/5, lambda in [3/5,7/8], y in [9/32,21/64], m=2/5: delta > 956608/1000000 > 0; B_balance > 15362/1000000 > 0.
  Comparison.ofRats ((956608 : Rat)/1000000) ((cellDelta a018)) .lt,
  -- A018.balance; A018: D=6/5, lambda in [3/5,7/8], y in [9/32,21/64], m=2/5: delta > 956608/1000000 > 0; B_balance > 15362/1000000 > 0.
  Comparison.ofRats ((15362 : Rat)/1000000) ((cellBalance a018)) .lt,
  -- A019.den; A019: D=6/5, lambda in [3/5,7/8], y in [21/64,3/8], m=49/100: delta > 936981/1000000 > 0; B_balance > 13269/1000000 > 0.
  Comparison.ofRats ((936981 : Rat)/1000000) ((cellDelta a019)) .lt,
  -- A019.balance; A019: D=6/5, lambda in [3/5,7/8], y in [21/64,3/8], m=49/100: delta > 936981/1000000 > 0; B_balance > 13269/1000000 > 0.
  Comparison.ofRats ((13269 : Rat)/1000000) ((cellBalance a019)) .lt,
  -- A020.den; A020: D=6/5, lambda in [3/5,7/8], y in [3/8,27/64], m=49/100: delta > 917480/1000000 > 0; B_balance > 20441/1000000 > 0.
  Comparison.ofRats ((917480 : Rat)/1000000) ((cellDelta a020)) .lt,
  -- A020.balance; A020: D=6/5, lambda in [3/5,7/8], y in [3/8,27/64], m=49/100: delta > 917480/1000000 > 0; B_balance > 20441/1000000 > 0.
  Comparison.ofRats ((20441 : Rat)/1000000) ((cellBalance a020)) .lt,
  -- A021.den; A021: D=6/5, lambda in [3/5,7/8], y in [27/64,15/32], m=49/100: delta > 898175/1000000 > 0; B_balance > 29334/1000000 > 0.
  Comparison.ofRats ((898175 : Rat)/1000000) ((cellDelta a021)) .lt,
  -- A021.balance; A021: D=6/5, lambda in [3/5,7/8], y in [27/64,15/32], m=49/100: delta > 898175/1000000 > 0; B_balance > 29334/1000000 > 0.
  Comparison.ofRats ((29334 : Rat)/1000000) ((cellBalance a021)) .lt,
  -- A022.den; A022: D=6/5, lambda in [3/5,7/8], y in [15/32,9/16], m=49/100: delta > 837498/1000000 > 0; B_balance > 11407/1000000 > 0.
  Comparison.ofRats ((837498 : Rat)/1000000) ((cellDelta a022)) .lt,
  -- A022.balance; A022: D=6/5, lambda in [3/5,7/8], y in [15/32,9/16], m=49/100: delta > 837498/1000000 > 0; B_balance > 11407/1000000 > 0.
  Comparison.ofRats ((11407 : Rat)/1000000) ((cellBalance a022)) .lt,
  -- A023.den; A023: D=6/5, lambda in [3/5,7/8], y in [9/16,21/32], m=49/100: delta > 799230/1000000 > 0; B_balance > 33024/1000000 > 0.
  Comparison.ofRats ((799230 : Rat)/1000000) ((cellDelta a023)) .lt,
  -- A023.balance; A023: D=6/5, lambda in [3/5,7/8], y in [9/16,21/32], m=49/100: delta > 799230/1000000 > 0; B_balance > 33024/1000000 > 0.
  Comparison.ofRats ((33024 : Rat)/1000000) ((cellBalance a023)) .lt,
  -- A024.den; A024: D=6/5, lambda in [3/5,7/8], y in [21/32,3/4], m=49/100: delta > 763114/1000000 > 0; B_balance > 63330/1000000 > 0.
  Comparison.ofRats ((763114 : Rat)/1000000) ((cellDelta a024)) .lt,
  -- A024.balance; A024: D=6/5, lambda in [3/5,7/8], y in [21/32,3/4], m=49/100: delta > 763114/1000000 > 0; B_balance > 63330/1000000 > 0.
  Comparison.ofRats ((63330 : Rat)/1000000) ((cellBalance a024)) .lt,
  -- A025.den; A025: D=6/5, lambda in [3/5,7/8], y in [3/4,27/32], m=49/100: delta > 729834/1000000 > 0; B_balance > 104635/1000000 > 0.
  Comparison.ofRats ((729834 : Rat)/1000000) ((cellDelta a025)) .lt,
  -- A025.balance; A025: D=6/5, lambda in [3/5,7/8], y in [3/4,27/32], m=49/100: delta > 729834/1000000 > 0; B_balance > 104635/1000000 > 0.
  Comparison.ofRats ((104635 : Rat)/1000000) ((cellBalance a025)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict062
