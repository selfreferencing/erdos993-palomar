module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict012

def records : List Comparison := [
  -- E053.lower; E053: 21169999/10000000 < E_minus(3/4); E_plus(3/4) < 21170002/10000000.
  Comparison.ofRats ((21169999 : Rat)/10000000) ((expLower (((3 : Rat) / (4 : Rat))))) .lt,
  -- E053.upper; E053: 21169999/10000000 < E_minus(3/4); E_plus(3/4) < 21170002/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (4 : Rat))))) ((21170002 : Rat)/10000000) .lt,
  -- E054.lower; E054: 21302726/10000000 < E_minus(121/160); E_plus(121/160) < 21302729/10000000.
  Comparison.ofRats ((21302726 : Rat)/10000000) ((expLower (((121 : Rat) / (160 : Rat))))) .lt,
  -- E054.upper; E054: 21302726/10000000 < E_minus(121/160); E_plus(121/160) < 21302729/10000000.
  Comparison.ofRats ((expUpper (((121 : Rat) / (160 : Rat))))) ((21302729 : Rat)/10000000) .lt,
  -- E055.lower; E055: 21419544/10000000 < E_minus(195/256); E_plus(195/256) < 21419547/10000000.
  Comparison.ofRats ((21419544 : Rat)/10000000) ((expLower (((195 : Rat) / (256 : Rat))))) .lt,
  -- E055.upper; E055: 21419544/10000000 < E_minus(195/256); E_plus(195/256) < 21419547/10000000.
  Comparison.ofRats ((expUpper (((195 : Rat) / (256 : Rat))))) ((21419547 : Rat)/10000000) .lt,
  -- E056.lower; E056: 21489942/10000000 < E_minus(153/200); E_plus(153/200) < 21489945/10000000.
  Comparison.ofRats ((21489942 : Rat)/10000000) ((expLower (((153 : Rat) / (200 : Rat))))) .lt,
  -- E056.upper; E056: 21489942/10000000 < E_minus(153/200); E_plus(153/200) < 21489945/10000000.
  Comparison.ofRats ((expUpper (((153 : Rat) / (200 : Rat))))) ((21489945 : Rat)/10000000) .lt,
  -- E057.lower; E057: 21672031/10000000 < E_minus(99/128); E_plus(99/128) < 21672034/10000000.
  Comparison.ofRats ((21672031 : Rat)/10000000) ((expLower (((99 : Rat) / (128 : Rat))))) .lt,
  -- E057.upper; E057: 21672031/10000000 < E_minus(99/128); E_plus(99/128) < 21672034/10000000.
  Comparison.ofRats ((expUpper (((99 : Rat) / (128 : Rat))))) ((21672034 : Rat)/10000000) .lt,
  -- E058.lower; E058: 21927494/10000000 < E_minus(201/256); E_plus(201/256) < 21927497/10000000.
  Comparison.ofRats ((21927494 : Rat)/10000000) ((expLower (((201 : Rat) / (256 : Rat))))) .lt,
  -- E058.upper; E058: 21927494/10000000 < E_minus(201/256); E_plus(201/256) < 21927497/10000000.
  Comparison.ofRats ((expUpper (((201 : Rat) / (256 : Rat))))) ((21927497 : Rat)/10000000) .lt,
  -- E059.lower; E059: 21978947/10000000 < E_minus(63/80); E_plus(63/80) < 21978950/10000000.
  Comparison.ofRats ((21978947 : Rat)/10000000) ((expLower (((63 : Rat) / (80 : Rat))))) .lt,
  -- E059.upper; E059: 21978947/10000000 < E_minus(63/80); E_plus(63/80) < 21978950/10000000.
  Comparison.ofRats ((expUpper (((63 : Rat) / (80 : Rat))))) ((21978950 : Rat)/10000000) .lt,
  -- E060.lower; E060: 22123658/10000000 < E_minus(2541/3200); E_plus(2541/3200) < 22123661/10000000.
  Comparison.ofRats ((22123658 : Rat)/10000000) ((expLower (((2541 : Rat) / (3200 : Rat))))) .lt,
  -- E060.upper; E060: 22123658/10000000 < E_minus(2541/3200); E_plus(2541/3200) < 22123661/10000000.
  Comparison.ofRats ((expUpper (((2541 : Rat) / (3200 : Rat))))) ((22123661 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict012
