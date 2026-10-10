module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict036

def records : List Comparison := [
  -- P096.lower; P096: lambda=28/25, y=87/64: 2528106/10000000 < L_minus(1+(28/25)/(4867199/1250000)); L_plus(1+(28/25)/(9734397/2500000)) < 2528111/10000000.
  Comparison.ofRats ((2528106 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4867199 : Rat) / (1250000 : Rat))))))) .lt,
  -- P096.upper; P096: lambda=28/25, y=87/64: 2528106/10000000 < L_minus(1+(28/25)/(4867199/1250000)); L_plus(1+(28/25)/(9734397/2500000)) < 2528111/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((9734397 : Rat) / (2500000 : Rat))))))) ((2528111 : Rat)/10000000) .lt,
  -- P097.lower; P097: lambda=28/25, y=45/32: 2425284/10000000 < L_minus(1+(28/25)/(20403123/5000000)); L_plus(1+(28/25)/(20403121/5000000)) < 2425289/10000000.
  Comparison.ofRats ((2425284 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20403123 : Rat) / (5000000 : Rat))))))) .lt,
  -- P097.upper; P097: lambda=28/25, y=45/32: 2425284/10000000 < L_minus(1+(28/25)/(20403123/5000000)); L_plus(1+(28/25)/(20403121/5000000)) < 2425289/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((20403121 : Rat) / (5000000 : Rat))))))) ((2425289 : Rat)/10000000) .lt,
  -- P098.lower; P098: lambda=28/25, y=93/64: 2326174/10000000 < L_minus(1+(28/25)/(42764579/10000000)); L_plus(1+(28/25)/(21382287/5000000)) < 2326179/10000000.
  Comparison.ofRats ((2326174 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((42764579 : Rat) / (10000000 : Rat))))))) .lt,
  -- P098.upper; P098: lambda=28/25, y=93/64: 2326174/10000000 < L_minus(1+(28/25)/(42764579/10000000)); L_plus(1+(28/25)/(21382287/5000000)) < 2326179/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((21382287 : Rat) / (5000000 : Rat))))))) ((2326179 : Rat)/10000000) .lt,
  -- P099.lower; P099: lambda=28/25, y=3/2: 2230679/10000000 < L_minus(1+(28/25)/(22408447/5000000)); L_plus(1+(28/25)/(44816889/10000000)) < 2230683/10000000.
  Comparison.ofRats ((2230679 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P099.upper; P099: lambda=28/25, y=3/2: 2230679/10000000 < L_minus(1+(28/25)/(22408447/5000000)); L_plus(1+(28/25)/(44816889/10000000)) < 2230683/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((2230683 : Rat)/10000000) .lt,
  -- P100.lower; P100: lambda=28/25, y=99/64: 2138699/10000000 < L_minus(1+(28/25)/(23483851/5000000)); L_plus(1+(28/25)/(46967697/10000000)) < 2138702/10000000.
  Comparison.ofRats ((2138699 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((23483851 : Rat) / (5000000 : Rat))))))) .lt,
  -- P100.upper; P100: lambda=28/25, y=99/64: 2138699/10000000 < L_minus(1+(28/25)/(23483851/5000000)); L_plus(1+(28/25)/(46967697/10000000)) < 2138702/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((46967697 : Rat) / (10000000 : Rat))))))) ((2138702 : Rat)/10000000) .lt,
  -- P101.lower; P101: lambda=28/25, y=51/32: 2050134/10000000 < L_minus(1+(28/25)/(4922173/1000000)); L_plus(1+(28/25)/(12305431/2500000)) < 2050138/10000000.
  Comparison.ofRats ((2050134 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((4922173 : Rat) / (1000000 : Rat))))))) .lt,
  -- P101.upper; P101: lambda=28/25, y=51/32: 2050134/10000000 < L_minus(1+(28/25)/(4922173/1000000)); L_plus(1+(28/25)/(12305431/2500000)) < 2050138/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((12305431 : Rat) / (2500000 : Rat))))))) ((2050138 : Rat)/10000000) .lt,
  -- P102.lower; P102: lambda=28/25, y=27/16: 1882862/10000000 < L_minus(1+(28/25)/(6757437/1250000)); L_plus(1+(28/25)/(1689359/312500)) < 1882865/10000000.
  Comparison.ofRats ((1882862 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((6757437 : Rat) / (1250000 : Rat))))))) .lt,
  -- P102.upper; P102: lambda=28/25, y=27/16: 1882862/10000000 < L_minus(1+(28/25)/(6757437/1250000)); L_plus(1+(28/25)/(1689359/312500)) < 1882865/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((1689359 : Rat) / (312500 : Rat))))))) ((1882865 : Rat)/10000000) .lt,
  -- P103.lower; P103: lambda=28/25, y=57/32: 1728086/10000000 < L_minus(1+(28/25)/(59372743/10000000)); L_plus(1+(28/25)/(14843183/2500000)) < 1728089/10000000.
  Comparison.ofRats ((1728086 : Rat)/10000000) ((logLower (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((59372743 : Rat) / (10000000 : Rat))))))) .lt,
  -- P103.upper; P103: lambda=28/25, y=57/32: 1728086/10000000 < L_minus(1+(28/25)/(59372743/10000000)); L_plus(1+(28/25)/(14843183/2500000)) < 1728089/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((28 : Rat) / (25 : Rat)) / ((14843183 : Rat) / (2500000 : Rat))))))) ((1728089 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict036
