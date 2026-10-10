module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict010

def records : List Comparison := [
  -- E037.lower; E037: 18828986/10000000 < E_minus(81/128); E_plus(81/128) < 18828989/10000000.
  Comparison.ofRats ((18828986 : Rat)/10000000) ((expLower (((81 : Rat) / (128 : Rat))))) .lt,
  -- E037.upper; E037: 18828986/10000000 < E_minus(81/128); E_plus(81/128) < 18828989/10000000.
  Comparison.ofRats ((expUpper (((81 : Rat) / (128 : Rat))))) ((18828989 : Rat)/10000000) .lt,
  -- E038.lower; E038: 18917454/10000000 < E_minus(51/80); E_plus(51/80) < 18917457/10000000.
  Comparison.ofRats ((18917454 : Rat)/10000000) ((expLower (((51 : Rat) / (80 : Rat))))) .lt,
  -- E038.upper; E038: 18917454/10000000 < E_minus(51/80); E_plus(51/80) < 18917457/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (80 : Rat))))) ((18917457 : Rat)/10000000) .lt,
  -- E039.lower; E039: 19050937/10000000 < E_minus(165/256); E_plus(165/256) < 19050940/10000000.
  Comparison.ofRats ((19050937 : Rat)/10000000) ((expLower (((165 : Rat) / (256 : Rat))))) .lt,
  -- E039.upper; E039: 19050937/10000000 < E_minus(165/256); E_plus(165/256) < 19050940/10000000.
  Comparison.ofRats ((expUpper (((165 : Rat) / (256 : Rat))))) ((19050940 : Rat)/10000000) .lt,
  -- E040.lower; E040: 19275503/10000000 < E_minus(21/32); E_plus(21/32) < 19275506/10000000.
  Comparison.ofRats ((19275503 : Rat)/10000000) ((expLower (((21 : Rat) / (32 : Rat))))) .lt,
  -- E040.upper; E040: 19275503/10000000 < E_minus(21/32); E_plus(21/32) < 19275506/10000000.
  Comparison.ofRats ((expUpper (((21 : Rat) / (32 : Rat))))) ((19275506 : Rat)/10000000) .lt,
  -- E041.lower; E041: 19502717/10000000 < E_minus(171/256); E_plus(171/256) < 19502720/10000000.
  Comparison.ofRats ((19502717 : Rat)/10000000) ((expLower (((171 : Rat) / (256 : Rat))))) .lt,
  -- E041.upper; E041: 19502717/10000000 < E_minus(171/256); E_plus(171/256) < 19502720/10000000.
  Comparison.ofRats ((expUpper (((171 : Rat) / (256 : Rat))))) ((19502720 : Rat)/10000000) .lt,
  -- E042.lower; E042: 19732608/10000000 < E_minus(87/128); E_plus(87/128) < 19732611/10000000.
  Comparison.ofRats ((19732608 : Rat)/10000000) ((expLower (((87 : Rat) / (128 : Rat))))) .lt,
  -- E042.upper; E042: 19732608/10000000 < E_minus(87/128); E_plus(87/128) < 19732611/10000000.
  Comparison.ofRats ((expUpper (((87 : Rat) / (128 : Rat))))) ((19732611 : Rat)/10000000) .lt,
  -- E043.lower; E043: 19788185/10000000 < E_minus(273/400); E_plus(273/400) < 19788188/10000000.
  Comparison.ofRats ((19788185 : Rat)/10000000) ((expLower (((273 : Rat) / (400 : Rat))))) .lt,
  -- E043.upper; E043: 19788185/10000000 < E_minus(273/400); E_plus(273/400) < 19788188/10000000.
  Comparison.ofRats ((expUpper (((273 : Rat) / (400 : Rat))))) ((19788188 : Rat)/10000000) .lt,
  -- E044.lower; E044: 19887373/10000000 < E_minus(11/16); E_plus(11/16) < 19887376/10000000.
  Comparison.ofRats ((19887373 : Rat)/10000000) ((expLower (((11 : Rat) / (16 : Rat))))) .lt,
  -- E044.upper; E044: 19887373/10000000 < E_minus(11/16); E_plus(11/16) < 19887376/10000000.
  Comparison.ofRats ((expUpper (((11 : Rat) / (16 : Rat))))) ((19887376 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict010
