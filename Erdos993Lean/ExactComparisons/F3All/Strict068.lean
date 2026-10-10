module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict068

def records : List Comparison := [
  -- A066.den; A066: D=6/5, lambda in [28/25,263/200], y in [33/64,69/128], m=49/100: delta > 825927/1000000 > 0; B_balance > 258/1000000 > 0.
  Comparison.ofRats ((825927 : Rat)/1000000) ((cellDelta a066)) .lt,
  -- A066.balance; A066: D=6/5, lambda in [28/25,263/200], y in [33/64,69/128], m=49/100: delta > 825927/1000000 > 0; B_balance > 258/1000000 > 0.
  Comparison.ofRats ((258 : Rat)/1000000) ((cellBalance a066)) .lt,
  -- A067.den; A067: D=6/5, lambda in [28/25,263/200], y in [69/128,9/16], m=49/100: delta > 815653/1000000 > 0; B_balance > 1277/1000000 > 0.
  Comparison.ofRats ((815653 : Rat)/1000000) ((cellDelta a067)) .lt,
  -- A067.balance; A067: D=6/5, lambda in [28/25,263/200], y in [69/128,9/16], m=49/100: delta > 815653/1000000 > 0; B_balance > 1277/1000000 > 0.
  Comparison.ofRats ((1277 : Rat)/1000000) ((cellBalance a067)) .lt,
  -- A068.den; A068: D=6/5, lambda in [28/25,263/200], y in [9/16,75/128], m=49/100: delta > 805381/1000000 > 0; B_balance > 2398/1000000 > 0.
  Comparison.ofRats ((805381 : Rat)/1000000) ((cellDelta a068)) .lt,
  -- A068.balance; A068: D=6/5, lambda in [28/25,263/200], y in [9/16,75/128], m=49/100: delta > 805381/1000000 > 0; B_balance > 2398/1000000 > 0.
  Comparison.ofRats ((2398 : Rat)/1000000) ((cellBalance a068)) .lt,
  -- A069.den; A069: D=6/5, lambda in [28/25,263/200], y in [75/128,39/64], m=49/100: delta > 795121/1000000 > 0; B_balance > 3620/1000000 > 0.
  Comparison.ofRats ((795121 : Rat)/1000000) ((cellDelta a069)) .lt,
  -- A069.balance; A069: D=6/5, lambda in [28/25,263/200], y in [75/128,39/64], m=49/100: delta > 795121/1000000 > 0; B_balance > 3620/1000000 > 0.
  Comparison.ofRats ((3620 : Rat)/1000000) ((cellBalance a069)) .lt,
  -- A070.den; A070: D=6/5, lambda in [28/25,263/200], y in [39/64,81/128], m=49/100: delta > 784881/1000000 > 0; B_balance > 4942/1000000 > 0.
  Comparison.ofRats ((784881 : Rat)/1000000) ((cellDelta a070)) .lt,
  -- A070.balance; A070: D=6/5, lambda in [28/25,263/200], y in [39/64,81/128], m=49/100: delta > 784881/1000000 > 0; B_balance > 4942/1000000 > 0.
  Comparison.ofRats ((4942 : Rat)/1000000) ((cellBalance a070)) .lt,
  -- A071.den; A071: D=6/5, lambda in [28/25,263/200], y in [81/128,21/32], m=49/100: delta > 774673/1000000 > 0; B_balance > 6364/1000000 > 0.
  Comparison.ofRats ((774673 : Rat)/1000000) ((cellDelta a071)) .lt,
  -- A071.balance; A071: D=6/5, lambda in [28/25,263/200], y in [81/128,21/32], m=49/100: delta > 774673/1000000 > 0; B_balance > 6364/1000000 > 0.
  Comparison.ofRats ((6364 : Rat)/1000000) ((cellBalance a071)) .lt,
  -- A072.den; A072: D=6/5, lambda in [28/25,263/200], y in [21/32,87/128], m=49/100: delta > 764504/1000000 > 0; B_balance > 7886/1000000 > 0.
  Comparison.ofRats ((764504 : Rat)/1000000) ((cellDelta a072)) .lt,
  -- A072.balance; A072: D=6/5, lambda in [28/25,263/200], y in [21/32,87/128], m=49/100: delta > 764504/1000000 > 0; B_balance > 7886/1000000 > 0.
  Comparison.ofRats ((7886 : Rat)/1000000) ((cellBalance a072)) .lt,
  -- A073.den; A073: D=6/5, lambda in [28/25,263/200], y in [87/128,45/64], m=49/100: delta > 754385/1000000 > 0; B_balance > 9506/1000000 > 0.
  Comparison.ofRats ((754385 : Rat)/1000000) ((cellDelta a073)) .lt,
  -- A073.balance; A073: D=6/5, lambda in [28/25,263/200], y in [87/128,45/64], m=49/100: delta > 754385/1000000 > 0; B_balance > 9506/1000000 > 0.
  Comparison.ofRats ((9506 : Rat)/1000000) ((cellBalance a073)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict068
