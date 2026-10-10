module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict015

def records : List Comparison := [
  -- E077.lower; E077: 23861649/10000000 < E_minus(2783/3200); E_plus(2783/3200) < 23861652/10000000.
  Comparison.ofRats ((23861649 : Rat)/10000000) ((expLower (((2783 : Rat) / (3200 : Rat))))) .lt,
  -- E077.upper; E077: 23861649/10000000 < E_minus(2783/3200); E_plus(2783/3200) < 23861652/10000000.
  Comparison.ofRats ((expUpper (((2783 : Rat) / (3200 : Rat))))) ((23861652 : Rat)/10000000) .lt,
  -- E078.lower; E078: 24082641/10000000 < E_minus(225/256); E_plus(225/256) < 24082644/10000000.
  Comparison.ofRats ((24082641 : Rat)/10000000) ((expLower (((225 : Rat) / (256 : Rat))))) .lt,
  -- E078.upper; E078: 24082641/10000000 < E_minus(225/256); E_plus(225/256) < 24082644/10000000.
  Comparison.ofRats ((expUpper (((225 : Rat) / (256 : Rat))))) ((24082644 : Rat)/10000000) .lt,
  -- E079.lower; E079: 24088286/10000000 < E_minus(11253/12800); E_plus(11253/12800) < 24088289/10000000.
  Comparison.ofRats ((24088286 : Rat)/10000000) ((expLower (((11253 : Rat) / (12800 : Rat))))) .lt,
  -- E079.upper; E079: 24088286/10000000 < E_minus(11253/12800); E_plus(11253/12800) < 24088289/10000000.
  Comparison.ofRats ((expUpper (((11253 : Rat) / (12800 : Rat))))) ((24088289 : Rat)/10000000) .lt,
  -- E080.lower; E080: 24317075/10000000 < E_minus(5687/6400); E_plus(5687/6400) < 24317078/10000000.
  Comparison.ofRats ((24317075 : Rat)/10000000) ((expLower (((5687 : Rat) / (6400 : Rat))))) .lt,
  -- E080.upper; E080: 24317075/10000000 < E_minus(5687/6400); E_plus(5687/6400) < 24317078/10000000.
  Comparison.ofRats ((expUpper (((5687 : Rat) / (6400 : Rat))))) ((24317078 : Rat)/10000000) .lt,
  -- E081.lower; E081: 24366519/10000000 < E_minus(57/64); E_plus(57/64) < 24366522/10000000.
  Comparison.ofRats ((24366519 : Rat)/10000000) ((expLower (((57 : Rat) / (64 : Rat))))) .lt,
  -- E081.upper; E081: 24366519/10000000 < E_minus(57/64); E_plus(57/64) < 24366522/10000000.
  Comparison.ofRats ((expUpper (((57 : Rat) / (64 : Rat))))) ((24366522 : Rat)/10000000) .lt,
  -- E082.lower; E082: 24412249/10000000 < E_minus(357/400); E_plus(357/400) < 24412252/10000000.
  Comparison.ofRats ((24412249 : Rat)/10000000) ((expLower (((357 : Rat) / (400 : Rat))))) .lt,
  -- E082.upper; E082: 24412249/10000000 < E_minus(357/400); E_plus(357/400) < 24412252/10000000.
  Comparison.ofRats ((expUpper (((357 : Rat) / (400 : Rat))))) ((24412252 : Rat)/10000000) .lt,
  -- E083.lower; E083: 24442784/10000000 < E_minus(143/160); E_plus(143/160) < 24442787/10000000.
  Comparison.ofRats ((24442784 : Rat)/10000000) ((expLower (((143 : Rat) / (160 : Rat))))) .lt,
  -- E083.upper; E083: 24442784/10000000 < E_minus(143/160); E_plus(143/160) < 24442787/10000000.
  Comparison.ofRats ((expUpper (((143 : Rat) / (160 : Rat))))) ((24442787 : Rat)/10000000) .lt,
  -- E084.lower; E084: 24781193/10000000 < E_minus(363/400); E_plus(363/400) < 24781196/10000000.
  Comparison.ofRats ((24781193 : Rat)/10000000) ((expLower (((363 : Rat) / (400 : Rat))))) .lt,
  -- E084.upper; E084: 24781193/10000000 < E_minus(363/400); E_plus(363/400) < 24781196/10000000.
  Comparison.ofRats ((expUpper (((363 : Rat) / (400 : Rat))))) ((24781196 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict015
