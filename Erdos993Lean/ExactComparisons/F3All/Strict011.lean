module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict011

def records : List Comparison := [
  -- E045.lower; E045: 19937154/10000000 < E_minus(69/100); E_plus(69/100) < 19937157/10000000.
  Comparison.ofRats ((19937154 : Rat)/10000000) ((expLower (((69 : Rat) / (100 : Rat))))) .lt,
  -- E045.upper; E045: 19937154/10000000 < E_minus(69/100); E_plus(69/100) < 19937157/10000000.
  Comparison.ofRats ((expUpper (((69 : Rat) / (100 : Rat))))) ((19937157 : Rat)/10000000) .lt,
  -- E046.lower; E046: 19965210/10000000 < E_minus(177/256); E_plus(177/256) < 19965213/10000000.
  Comparison.ofRats ((19965210 : Rat)/10000000) ((expLower (((177 : Rat) / (256 : Rat))))) .lt,
  -- E046.upper; E046: 19965210/10000000 < E_minus(177/256); E_plus(177/256) < 19965213/10000000.
  Comparison.ofRats ((expUpper (((177 : Rat) / (256 : Rat))))) ((19965213 : Rat)/10000000) .lt,
  -- E047.lower; E047: 20200554/10000000 < E_minus(45/64); E_plus(45/64) < 20200557/10000000.
  Comparison.ofRats ((20200554 : Rat)/10000000) ((expLower (((45 : Rat) / (64 : Rat))))) .lt,
  -- E047.upper; E047: 20200554/10000000 < E_minus(45/64); E_plus(45/64) < 20200557/10000000.
  Comparison.ofRats ((expUpper (((45 : Rat) / (64 : Rat))))) ((20200557 : Rat)/10000000) .lt,
  -- E048.lower; E048: 20438672/10000000 < E_minus(183/256); E_plus(183/256) < 20438675/10000000.
  Comparison.ofRats ((20438672 : Rat)/10000000) ((expLower (((183 : Rat) / (256 : Rat))))) .lt,
  -- E048.upper; E048: 20438672/10000000 < E_minus(183/256); E_plus(183/256) < 20438675/10000000.
  Comparison.ofRats ((expUpper (((183 : Rat) / (256 : Rat))))) ((20438675 : Rat)/10000000) .lt,
  -- E049.lower; E049: 20679596/10000000 < E_minus(93/128); E_plus(93/128) < 20679599/10000000.
  Comparison.ofRats ((20679596 : Rat)/10000000) ((expLower (((93 : Rat) / (128 : Rat))))) .lt,
  -- E049.upper; E049: 20679596/10000000 < E_minus(93/128); E_plus(93/128) < 20679599/10000000.
  Comparison.ofRats ((expUpper (((93 : Rat) / (128 : Rat))))) ((20679599 : Rat)/10000000) .lt,
  -- E050.lower; E050: 20854818/10000000 < E_minus(147/200); E_plus(147/200) < 20854821/10000000.
  Comparison.ofRats ((20854818 : Rat)/10000000) ((expLower (((147 : Rat) / (200 : Rat))))) .lt,
  -- E050.upper; E050: 20854818/10000000 < E_minus(147/200); E_plus(147/200) < 20854821/10000000.
  Comparison.ofRats ((expUpper (((147 : Rat) / (200 : Rat))))) ((20854821 : Rat)/10000000) .lt,
  -- E051.lower; E051: 20923361/10000000 < E_minus(189/256); E_plus(189/256) < 20923364/10000000.
  Comparison.ofRats ((20923361 : Rat)/10000000) ((expLower (((189 : Rat) / (256 : Rat))))) .lt,
  -- E051.upper; E051: 20923361/10000000 < E_minus(189/256); E_plus(189/256) < 20923364/10000000.
  Comparison.ofRats ((expUpper (((189 : Rat) / (256 : Rat))))) ((20923364 : Rat)/10000000) .lt,
  -- E052.lower; E052: 21117140/10000000 < E_minus(299/400); E_plus(299/400) < 21117143/10000000.
  Comparison.ofRats ((21117140 : Rat)/10000000) ((expLower (((299 : Rat) / (400 : Rat))))) .lt,
  -- E052.upper; E052: 21117140/10000000 < E_minus(299/400); E_plus(299/400) < 21117143/10000000.
  Comparison.ofRats ((expUpper (((299 : Rat) / (400 : Rat))))) ((21117143 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict011
