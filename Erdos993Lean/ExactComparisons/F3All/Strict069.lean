module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict069

def records : List Comparison := [
  -- A074.den; A074: D=6/5, lambda in [28/25,263/200], y in [45/64,93/128], m=49/100: delta > 744327/1000000 > 0; B_balance > 11227/1000000 > 0.
  Comparison.ofRats ((744327 : Rat)/1000000) ((cellDelta a074)) .lt,
  -- A074.balance; A074: D=6/5, lambda in [28/25,263/200], y in [45/64,93/128], m=49/100: delta > 744327/1000000 > 0; B_balance > 11227/1000000 > 0.
  Comparison.ofRats ((11227 : Rat)/1000000) ((cellBalance a074)) .lt,
  -- A075.den; A075: D=6/5, lambda in [28/25,263/200], y in [93/128,3/4], m=49/100: delta > 734338/1000000 > 0; B_balance > 13050/1000000 > 0.
  Comparison.ofRats ((734338 : Rat)/1000000) ((cellDelta a075)) .lt,
  -- A075.balance; A075: D=6/5, lambda in [28/25,263/200], y in [93/128,3/4], m=49/100: delta > 734338/1000000 > 0; B_balance > 13050/1000000 > 0.
  Comparison.ofRats ((13050 : Rat)/1000000) ((cellBalance a075)) .lt,
  -- A076.den; A076: D=6/5, lambda in [28/25,263/200], y in [3/4,99/128], m=49/100: delta > 724432/1000000 > 0; B_balance > 15186/1000000 > 0.
  Comparison.ofRats ((724432 : Rat)/1000000) ((cellDelta a076)) .lt,
  -- A076.balance; A076: D=6/5, lambda in [28/25,263/200], y in [3/4,99/128], m=49/100: delta > 724432/1000000 > 0; B_balance > 15186/1000000 > 0.
  Comparison.ofRats ((15186 : Rat)/1000000) ((cellBalance a076)) .lt,
  -- A077.den; A077: D=6/5, lambda in [28/25,263/200], y in [99/128,51/64], m=49/100: delta > 714617/1000000 > 0; B_balance > 17444/1000000 > 0.
  Comparison.ofRats ((714617 : Rat)/1000000) ((cellDelta a077)) .lt,
  -- A077.balance; A077: D=6/5, lambda in [28/25,263/200], y in [99/128,51/64], m=49/100: delta > 714617/1000000 > 0; B_balance > 17444/1000000 > 0.
  Comparison.ofRats ((17444 : Rat)/1000000) ((cellBalance a077)) .lt,
  -- A078.den; A078: D=6/5, lambda in [28/25,263/200], y in [51/64,105/128], m=49/100: delta > 704905/1000000 > 0; B_balance > 19816/1000000 > 0.
  Comparison.ofRats ((704905 : Rat)/1000000) ((cellDelta a078)) .lt,
  -- A078.balance; A078: D=6/5, lambda in [28/25,263/200], y in [51/64,105/128], m=49/100: delta > 704905/1000000 > 0; B_balance > 19816/1000000 > 0.
  Comparison.ofRats ((19816 : Rat)/1000000) ((cellBalance a078)) .lt,
  -- A079.den; A079: D=6/5, lambda in [28/25,263/200], y in [105/128,27/32], m=49/100: delta > 695307/1000000 > 0; B_balance > 22310/1000000 > 0.
  Comparison.ofRats ((695307 : Rat)/1000000) ((cellDelta a079)) .lt,
  -- A079.balance; A079: D=6/5, lambda in [28/25,263/200], y in [105/128,27/32], m=49/100: delta > 695307/1000000 > 0; B_balance > 22310/1000000 > 0.
  Comparison.ofRats ((22310 : Rat)/1000000) ((cellBalance a079)) .lt,
  -- A080.den; A080: D=6/5, lambda in [28/25,263/200], y in [27/32,111/128], m=49/100: delta > 685835/1000000 > 0; B_balance > 24900/1000000 > 0.
  Comparison.ofRats ((685835 : Rat)/1000000) ((cellDelta a080)) .lt,
  -- A080.balance; A080: D=6/5, lambda in [28/25,263/200], y in [27/32,111/128], m=49/100: delta > 685835/1000000 > 0; B_balance > 24900/1000000 > 0.
  Comparison.ofRats ((24900 : Rat)/1000000) ((cellBalance a080)) .lt,
  -- A081.den; A081: D=6/5, lambda in [28/25,263/200], y in [111/128,57/64], m=49/100: delta > 676502/1000000 > 0; B_balance > 27607/1000000 > 0.
  Comparison.ofRats ((676502 : Rat)/1000000) ((cellDelta a081)) .lt,
  -- A081.balance; A081: D=6/5, lambda in [28/25,263/200], y in [111/128,57/64], m=49/100: delta > 676502/1000000 > 0; B_balance > 27607/1000000 > 0.
  Comparison.ofRats ((27607 : Rat)/1000000) ((cellBalance a081)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict069
