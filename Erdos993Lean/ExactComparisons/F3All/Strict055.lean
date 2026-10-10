module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict055

def records : List Comparison := [
  -- P248.lower; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats ((2597837 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((629249 : Rat) / (80000 : Rat))))))) .lt,
  -- P248.upper; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((78656091 : Rat) / (10000000 : Rat))))))) ((2597843 : Rat)/10000000) .lt,
  -- P249.lower; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats ((2198831 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((23719357 : Rat) / (2500000 : Rat))))))) .lt,
  -- P249.upper; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((94877357 : Rat) / (10000000 : Rat))))))) ((2198836 : Rat)/10000000) .lt,
  -- P250.lower; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats ((1561705 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((27609207 : Rat) / (2000000 : Rat))))))) .lt,
  -- P250.upper; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((6902287 : Rat) / (500000 : Rat))))))) ((1561712 : Rat)/10000000) .lt,
  -- P251.lower; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats ((1099023 : Rat)/10000000) ((logLower (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((100428229 : Rat) / (5000000 : Rat))))))) .lt,
  -- P251.upper; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((7 : Rat) / (3 : Rat)) / ((40171073 : Rat) / (2000000 : Rat))))))) ((1099032 : Rat)/10000000) .lt,
  -- C001.ell; C001: D=6/5, v=263/200, y in [0,21/50], type L: ell_star > 208674/1000000 > 0.
  Comparison.ofRats ((208674 : Rat)/1000000) ((faceEll c001)) .lt,
  -- C002.ell; C002: D=6/5, v=263/200, y in [21/50,63/100], type L: ell_star > 31406/1000000 > 0.
  Comparison.ofRats ((31406 : Rat)/1000000) ((faceEll c002)) .lt,
  -- C003.den; C003: D=6/5, v=263/200, y in [63/100,273/400], type C: d0 > 997182/1000000 > 0; C_balance > 4069/1000000 > 0.
  Comparison.ofRats ((997182 : Rat)/1000000) ((faceDen c003)) .lt,
  -- C003.balance; C003: D=6/5, v=263/200, y in [63/100,273/400], type C: d0 > 997182/1000000 > 0; C_balance > 4069/1000000 > 0.
  Comparison.ofRats ((4069 : Rat)/1000000) ((faceBalance c003)) .lt,
  -- C004.den; C004: D=6/5, v=263/200, y in [273/400,147/200], type C: d0 > 976324/1000000 > 0; C_balance > 791/1000000 > 0.
  Comparison.ofRats ((976324 : Rat)/1000000) ((faceDen c004)) .lt,
  -- C004.balance; C004: D=6/5, v=263/200, y in [273/400,147/200], type C: d0 > 976324/1000000 > 0; C_balance > 791/1000000 > 0.
  Comparison.ofRats ((791 : Rat)/1000000) ((faceBalance c004)) .lt,
  -- C005.den; C005: D=6/5, v=263/200, y in [147/200,63/80], type C: d0 > 955748/1000000 > 0; C_balance > 3588/1000000 > 0.
  Comparison.ofRats ((955748 : Rat)/1000000) ((faceDen c005)) .lt,
  -- C005.balance; C005: D=6/5, v=263/200, y in [147/200,63/80], type C: d0 > 955748/1000000 > 0; C_balance > 3588/1000000 > 0.
  Comparison.ofRats ((3588 : Rat)/1000000) ((faceBalance c005)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict055
