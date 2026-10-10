module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict022

def records : List Comparison := [
  -- E133.lower; E133: 75054166/10000000 < E_minus(129/64); E_plus(129/64) < 75054194/10000000.
  Comparison.ofRats ((75054166 : Rat)/10000000) ((expLower (((129 : Rat) / (64 : Rat))))) .lt,
  -- E133.upper; E133: 75054166/10000000 < E_minus(129/64); E_plus(129/64) < 75054194/10000000.
  Comparison.ofRats ((expUpper (((129 : Rat) / (64 : Rat))))) ((75054194 : Rat)/10000000) .lt,
  -- E134.lower; E134: 78656091/10000000 < E_minus(33/16); E_plus(33/16) < 78656125/10000000.
  Comparison.ofRats ((78656091 : Rat)/10000000) ((expLower (((33 : Rat) / (16 : Rat))))) .lt,
  -- E134.upper; E134: 78656091/10000000 < E_minus(33/16); E_plus(33/16) < 78656125/10000000.
  Comparison.ofRats ((expUpper (((33 : Rat) / (16 : Rat))))) ((78656125 : Rat)/10000000) .lt,
  -- E135.lower; E135: 86386816/10000000 < E_minus(69/32); E_plus(69/32) < 86386865/10000000.
  Comparison.ofRats ((86386816 : Rat)/10000000) ((expLower (((69 : Rat) / (32 : Rat))))) .lt,
  -- E135.upper; E135: 86386816/10000000 < E_minus(69/32); E_plus(69/32) < 86386865/10000000.
  Comparison.ofRats ((expUpper (((69 : Rat) / (32 : Rat))))) ((86386865 : Rat)/10000000) .lt,
  -- E136.lower; E136: 94877357/10000000 < E_minus(9/4); E_plus(9/4) < 94877428/10000000.
  Comparison.ofRats ((94877357 : Rat)/10000000) ((expLower (((9 : Rat) / (4 : Rat))))) .lt,
  -- E136.upper; E136: 94877357/10000000 < E_minus(9/4); E_plus(9/4) < 94877428/10000000.
  Comparison.ofRats ((expUpper (((9 : Rat) / (4 : Rat))))) ((94877428 : Rat)/10000000) .lt,
  -- E137.lower; E137: 114443938/10000000 < E_minus(39/16); E_plus(39/16) < 114444085/10000000.
  Comparison.ofRats ((114443938 : Rat)/10000000) ((expLower (((39 : Rat) / (16 : Rat))))) .lt,
  -- E137.upper; E137: 114443938/10000000 < E_minus(39/16); E_plus(39/16) < 114444085/10000000.
  Comparison.ofRats ((expUpper (((39 : Rat) / (16 : Rat))))) ((114444085 : Rat)/10000000) .lt,
  -- E138.lower; E138: 138045740/10000000 < E_minus(21/8); E_plus(21/8) < 138046035/10000000.
  Comparison.ofRats ((138045740 : Rat)/10000000) ((expLower (((21 : Rat) / (8 : Rat))))) .lt,
  -- E138.upper; E138: 138045740/10000000 < E_minus(21/8); E_plus(21/8) < 138046035/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (8 : Rat))))) ((138046035 : Rat)/10000000) .lt,
  -- E139.lower; E139: 166514947/10000000 < E_minus(45/16); E_plus(45/16) < 166515523/10000000.
  Comparison.ofRats ((166514947 : Rat)/10000000) ((expLower (((45 : Rat) / (16 : Rat))))) .lt,
  -- E139.upper; E139: 166514947/10000000 < E_minus(45/16); E_plus(45/16) < 166515523/10000000.
  Comparison.ofRats ((expUpper (((45 : Rat) / (16 : Rat))))) ((166515523 : Rat)/10000000) .lt,
  -- E140.lower; E140: 200855365/10000000 < E_minus(3); E_plus(3) < 200856458/10000000.
  Comparison.ofRats ((200855365 : Rat)/10000000) ((expLower ((3 : Rat)))) .lt,
  -- E140.upper; E140: 200855365/10000000 < E_minus(3); E_plus(3) < 200856458/10000000.
  Comparison.ofRats ((expUpper ((3 : Rat)))) ((200856458 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict022
