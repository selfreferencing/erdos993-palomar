module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict005

def records : List Comparison := [
  -- F65: 32/7-91/240-25/42=6043/1680>0    [childless derivative, y>=1]
  Comparison.ofRats ((0 : Rat)) (((((32 : Rat) / (7 : Rat)) - ((91 : Rat) / (240 : Rat))) - ((25 : Rat) / (42 : Rat)))) .lt,
  -- F66: 120/91-1=29/91>0    [AC child envelope denominator]
  Comparison.ofRats ((0 : Rat)) ((((120 : Rat) / (91 : Rat)) - (1 : Rat))) .lt,
  -- F67: 7/25-1/10=9/50>0    [T0 curvature]
  Comparison.ofRats ((0 : Rat)) ((((7 : Rat) / (25 : Rat)) - ((1 : Rat) / (10 : Rat)))) .lt,
  -- F68: \beta_+(1/3)<5/4    [T0 curvature, prefix activity endpoint]
  Comparison.ofRats (b01.hi) (((5 : Rat) / (4 : Rat))) .lt,
  -- F69: \beta_+(3/5)<5/4    [T0 curvature, prefix activity endpoint]
  Comparison.ofRats (b02.hi) (((5 : Rat) / (4 : Rat))) .lt,
  -- F70: \beta_+(7/8)<5/4    [T0 curvature, prefix activity endpoint]
  Comparison.ofRats (b03.hi) (((5 : Rat) / (4 : Rat))) .lt,
  -- F71: \beta_+(28/25)<5/4    [T0 curvature, prefix activity endpoint]
  Comparison.ofRats (b04.hi) (((5 : Rat) / (4 : Rat))) .lt,
  -- F72: 121/100<5/4    [all five CA cover tops]
  Comparison.ofRats (((121 : Rat) / (100 : Rat))) (((5 : Rat) / (4 : Rat))) .lt,
  -- E001.lower; E001: 10479909/10000000 < E_minus(3/64); E_plus(3/64) < 10479912/10000000.
  Comparison.ofRats ((10479909 : Rat)/10000000) ((expLower (((3 : Rat) / (64 : Rat))))) .lt,
  -- E001.upper; E001: 10479909/10000000 < E_minus(3/64); E_plus(3/64) < 10479912/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (64 : Rat))))) ((10479912 : Rat)/10000000) .lt,
  -- E002.lower; E002: 10982850/10000000 < E_minus(3/32); E_plus(3/32) < 10982853/10000000.
  Comparison.ofRats ((10982850 : Rat)/10000000) ((expLower (((3 : Rat) / (32 : Rat))))) .lt,
  -- E002.upper; E002: 10982850/10000000 < E_minus(3/32); E_plus(3/32) < 10982853/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (32 : Rat))))) ((10982853 : Rat)/10000000) .lt,
  -- E003.lower; E003: 11509928/10000000 < E_minus(9/64); E_plus(9/64) < 11509931/10000000.
  Comparison.ofRats ((11509928 : Rat)/10000000) ((expLower (((9 : Rat) / (64 : Rat))))) .lt,
  -- E003.upper; E003: 11509928/10000000 < E_minus(9/64); E_plus(9/64) < 11509931/10000000.
  Comparison.ofRats ((expUpper (((9 : Rat) / (64 : Rat))))) ((11509931 : Rat)/10000000) .lt,
  -- E004.lower; E004: 12062301/10000000 < E_minus(3/16); E_plus(3/16) < 12062304/10000000.
  Comparison.ofRats ((12062301 : Rat)/10000000) ((expLower (((3 : Rat) / (16 : Rat))))) .lt,
  -- E004.upper; E004: 12062301/10000000 < E_minus(3/16); E_plus(3/16) < 12062304/10000000.
  Comparison.ofRats ((expUpper (((3 : Rat) / (16 : Rat))))) ((12062304 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict005
