module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict023

def records : List Comparison := [
  -- B01.lower; B01: 2876818/10000000 < L_minus(1+(1/3)); L_plus(1+(1/3)) < 2876823/10000000.
  Comparison.ofRats ((2876818 : Rat)/10000000) ((logLower (((1 : Rat) + ((1 : Rat) / (3 : Rat)))))) .lt,
  -- B01.upper; B01: 2876818/10000000 < L_minus(1+(1/3)); L_plus(1+(1/3)) < 2876823/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((1 : Rat) / (3 : Rat)))))) ((2876823 : Rat)/10000000) .lt,
  -- B02.lower; B02: 4700034/10000000 < L_minus(1+(3/5)); L_plus(1+(3/5)) < 4700039/10000000.
  Comparison.ofRats ((4700034 : Rat)/10000000) ((logLower (((1 : Rat) + ((3 : Rat) / (5 : Rat)))))) .lt,
  -- B02.upper; B02: 4700034/10000000 < L_minus(1+(3/5)); L_plus(1+(3/5)) < 4700039/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((3 : Rat) / (5 : Rat)))))) ((4700039 : Rat)/10000000) .lt,
  -- B03.lower; B03: 6286083/10000000 < L_minus(1+(7/8)); L_plus(1+(7/8)) < 6286089/10000000.
  Comparison.ofRats ((6286083 : Rat)/10000000) ((logLower (((1 : Rat) + ((7 : Rat) / (8 : Rat)))))) .lt,
  -- B03.upper; B03: 6286083/10000000 < L_minus(1+(7/8)); L_plus(1+(7/8)) < 6286089/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((7 : Rat) / (8 : Rat)))))) ((6286089 : Rat)/10000000) .lt,
  -- B04.lower; B04: 7514155/10000000 < L_minus(1+(28/25)); L_plus(1+(28/25)) < 7514163/10000000.
  Comparison.ofRats ((7514155 : Rat)/10000000) ((logLower (((1 : Rat) + ((28 : Rat) / (25 : Rat)))))) .lt,
  -- B04.upper; B04: 7514155/10000000 < L_minus(1+(28/25)); L_plus(1+(28/25)) < 7514163/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((28 : Rat) / (25 : Rat)))))) ((7514163 : Rat)/10000000) .lt,
  -- B05.lower; B05: 8394091/10000000 < L_minus(1+(263/200)); L_plus(1+(263/200)) < 8394099/10000000.
  Comparison.ofRats ((8394091 : Rat)/10000000) ((logLower (((1 : Rat) + ((263 : Rat) / (200 : Rat)))))) .lt,
  -- B05.upper; B05: 8394091/10000000 < L_minus(1+(263/200)); L_plus(1+(263/200)) < 8394099/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((263 : Rat) / (200 : Rat)))))) ((8394099 : Rat)/10000000) .lt,
  -- B06.lower; B06: 9162900/10000000 < L_minus(1+(3/2)); L_plus(1+(3/2)) < 9162909/10000000.
  Comparison.ofRats ((9162900 : Rat)/10000000) ((logLower (((1 : Rat) + ((3 : Rat) / (2 : Rat)))))) .lt,
  -- B06.upper; B06: 9162900/10000000 < L_minus(1+(3/2)); L_plus(1+(3/2)) < 9162909/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((3 : Rat) / (2 : Rat)))))) ((9162909 : Rat)/10000000) .lt,
  -- B07.lower; B07: 10116001/10000000 < L_minus(1+(7/4)); L_plus(1+(7/4)) < 10116011/10000000.
  Comparison.ofRats ((10116001 : Rat)/10000000) ((logLower (((1 : Rat) + ((7 : Rat) / (4 : Rat)))))) .lt,
  -- B07.upper; B07: 10116001/10000000 < L_minus(1+(7/4)); L_plus(1+(7/4)) < 10116011/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + ((7 : Rat) / (4 : Rat)))))) ((10116011 : Rat)/10000000) .lt,
  -- B08.lower; B08: 10986116/10000000 < L_minus(1+(2)); L_plus(1+(2)) < 10986125/10000000.
  Comparison.ofRats ((10986116 : Rat)/10000000) ((logLower (((1 : Rat) + (2 : Rat))))) .lt,
  -- B08.upper; B08: 10986116/10000000 < L_minus(1+(2)); L_plus(1+(2)) < 10986125/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (2 : Rat))))) ((10986125 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict023
