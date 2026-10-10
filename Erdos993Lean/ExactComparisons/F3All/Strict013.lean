module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict013

def records : List Comparison := [
  -- E061.lower; E061: 22185968/10000000 < E_minus(51/64); E_plus(51/64) < 22185971/10000000.
  Comparison.ofRats ((22185968 : Rat)/10000000) ((expLower (((51 : Rat) / (64 : Rat))))) .lt,
  -- E061.upper; E061: 22185968/10000000 < E_minus(51/64); E_plus(51/64) < 22185971/10000000.
  Comparison.ofRats ((expUpper (((51 : Rat) / (64 : Rat))))) ((22185971 : Rat)/10000000) .lt,
  -- E062.lower; E062: 22366963/10000000 < E_minus(161/200); E_plus(161/200) < 22366967/10000000.
  Comparison.ofRats ((22366963 : Rat)/10000000) ((expLower (((161 : Rat) / (200 : Rat))))) .lt,
  -- E062.upper; E062: 22366963/10000000 < E_minus(161/200); E_plus(161/200) < 22366967/10000000.
  Comparison.ofRats ((expUpper (((161 : Rat) / (200 : Rat))))) ((22366967 : Rat)/10000000) .lt,
  -- E063.lower; E063: 22447489/10000000 < E_minus(207/256); E_plus(207/256) < 22447492/10000000.
  Comparison.ofRats ((22447489 : Rat)/10000000) ((expLower (((207 : Rat) / (256 : Rat))))) .lt,
  -- E063.upper; E063: 22447489/10000000 < E_minus(207/256); E_plus(207/256) < 22447492/10000000.
  Comparison.ofRats ((expUpper (((207 : Rat) / (256 : Rat))))) ((22447492 : Rat)/10000000) .lt,
  -- E064.lower; E064: 22545912/10000000 < E_minus(5203/6400); E_plus(5203/6400) < 22545915/10000000.
  Comparison.ofRats ((22545912 : Rat)/10000000) ((expLower (((5203 : Rat) / (6400 : Rat))))) .lt,
  -- E064.upper; E064: 22545912/10000000 < E_minus(5203/6400); E_plus(5203/6400) < 22545915/10000000.
  Comparison.ofRats ((expUpper (((5203 : Rat) / (6400 : Rat))))) ((22545915 : Rat)/10000000) .lt,
  -- E065.lower; E065: 22712093/10000000 < E_minus(105/128); E_plus(105/128) < 22712096/10000000.
  Comparison.ofRats ((22712093 : Rat)/10000000) ((expLower (((105 : Rat) / (128 : Rat))))) .lt,
  -- E065.upper; E065: 22712093/10000000 < E_minus(105/128); E_plus(105/128) < 22712096/10000000.
  Comparison.ofRats ((expUpper (((105 : Rat) / (128 : Rat))))) ((22712096 : Rat)/10000000) .lt,
  -- E066.lower; E066: 22818806/10000000 < E_minus(33/40); E_plus(33/40) < 22818809/10000000.
  Comparison.ofRats ((22818806 : Rat)/10000000) ((expLower (((33 : Rat) / (40 : Rat))))) .lt,
  -- E066.upper; E066: 22818806/10000000 < E_minus(33/40); E_plus(33/40) < 22818809/10000000.
  Comparison.ofRats ((expUpper (((33 : Rat) / (40 : Rat))))) ((22818809 : Rat)/10000000) .lt,
  -- E067.lower; E067: 22904537/10000000 < E_minus(663/800); E_plus(663/800) < 22904540/10000000.
  Comparison.ofRats ((22904537 : Rat)/10000000) ((expLower (((663 : Rat) / (800 : Rat))))) .lt,
  -- E067.upper; E067: 22904537/10000000 < E_minus(663/800); E_plus(663/800) < 22904540/10000000.
  Comparison.ofRats ((expUpper (((663 : Rat) / (800 : Rat))))) ((22904540 : Rat)/10000000) .lt,
  -- E068.lower; E068: 22976226/10000000 < E_minus(1331/1600); E_plus(1331/1600) < 22976229/10000000.
  Comparison.ofRats ((22976226 : Rat)/10000000) ((expLower (((1331 : Rat) / (1600 : Rat))))) .lt,
  -- E068.upper; E068: 22976226/10000000 < E_minus(1331/1600); E_plus(1331/1600) < 22976229/10000000.
  Comparison.ofRats ((expUpper (((1331 : Rat) / (1600 : Rat))))) ((22976229 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict013
