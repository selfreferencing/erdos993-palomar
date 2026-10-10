module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict024

def records : List Comparison := [
  -- B09.lower; B09: 12039721/10000000 < L_minus(1+(7/3)); L_plus(1+(7/3)) < 12039731/10000000.
  Comparison.ofRats ((12039721 : Rat)/10000000) ((logLower (((1 : Rat) + ((7 : Rat) / (3 : Rat)))))) .lt,
  -- B09.upper; B09: 12039721/10000000 < L_minus(1+(7/3)); L_plus(1+(7/3)) < 12039731/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((7 : Rat) / (3 : Rat)))))) ((12039731 : Rat)/10000000) .lt,
  -- P001.lower; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats ((2650553 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((10982853 : Rat) / (10000000 : Rat))))))) .lt,
  -- P001.upper; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((219657 : Rat) / (200000 : Rat))))))) ((2650558 : Rat)/10000000) .lt,
  -- P002.lower; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats ((2439987 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((376947 : Rat) / (312500 : Rat))))))) .lt,
  -- P002.upper; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((12062301 : Rat) / (10000000 : Rat))))))) ((2439992 : Rat)/10000000) .lt,
  -- P003.lower; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats ((2340344 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6320593 : Rat) / (5000000 : Rat))))))) .lt,
  -- P003.upper; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((12641183 : Rat) / (10000000 : Rat))))))) ((2340349 : Rat)/10000000) .lt,
  -- P004.lower; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats ((2244330 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((13247849 : Rat) / (10000000 : Rat))))))) .lt,
  -- P004.upper; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((6623923 : Rat) / (5000000 : Rat))))))) ((2244335 : Rat)/10000000) .lt,
  -- P005.lower; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats ((2062791 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3637479 : Rat) / (2500000 : Rat))))))) .lt,
  -- P005.upper; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((14549913 : Rat) / (10000000 : Rat))))))) ((2062795 : Rat)/10000000) .lt,
  -- P006.lower; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats ((1894581 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3994989 : Rat) / (2500000 : Rat))))))) .lt,
  -- P006.upper; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((15979953 : Rat) / (10000000 : Rat))))))) ((1894584 : Rat)/10000000) .lt,
  -- P007.lower; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats ((1738923 : Rat)/10000000) ((logLower (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((4387637 : Rat) / (2500000 : Rat))))))) .lt,
  -- P007.upper; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((1 : Rat) / (3 : Rat)) / ((3510109 : Rat) / (2000000 : Rat))))))) ((1738926 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict024
