module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Strict042

def records : List Comparison := [
  -- P144.lower; P144: lambda=263/200, y=81/64: 3154765/10000000 < L_minus(1+(263/200)/(35453081/10000000)); L_plus(1+(263/200)/(35453077/10000000)) < 3154770/10000000.
  Comparison.ofRats ((3154765 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((35453081 : Rat) / (10000000 : Rat))))))) .lt,
  -- P144.upper; P144: lambda=263/200, y=81/64: 3154765/10000000 < L_minus(1+(263/200)/(35453081/10000000)); L_plus(1+(263/200)/(35453077/10000000)) < 3154770/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((35453077 : Rat) / (10000000 : Rat))))))) ((3154770 : Rat)/10000000) .lt,
  -- P145.lower; P145: lambda=263/200, y=21/16: 3030093/10000000 < L_minus(1+(263/200)/(37154509/10000000)); L_plus(1+(263/200)/(18577253/5000000)) < 3030098/10000000.
  Comparison.ofRats ((3030093 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((37154509 : Rat) / (10000000 : Rat))))))) .lt,
  -- P145.upper; P145: lambda=263/200, y=21/16: 3030093/10000000 < L_minus(1+(263/200)/(37154509/10000000)); L_plus(1+(263/200)/(18577253/5000000)) < 3030098/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((18577253 : Rat) / (5000000 : Rat))))))) ((3030098 : Rat)/10000000) .lt,
  -- P146.lower; P146: lambda=263/200, y=87/64: 2909663/10000000 < L_minus(1+(263/200)/(4867199/1250000)); L_plus(1+(263/200)/(9734397/2500000)) < 2909668/10000000.
  Comparison.ofRats ((2909663 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4867199 : Rat) / (1250000 : Rat))))))) .lt,
  -- P146.upper; P146: lambda=263/200, y=87/64: 2909663/10000000 < L_minus(1+(263/200)/(4867199/1250000)); L_plus(1+(263/200)/(9734397/2500000)) < 2909668/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((9734397 : Rat) / (2500000 : Rat))))))) ((2909668 : Rat)/10000000) .lt,
  -- P147.lower; P147: lambda=263/200, y=45/32: 2793380/10000000 < L_minus(1+(263/200)/(20403123/5000000)); L_plus(1+(263/200)/(20403121/5000000)) < 2793385/10000000.
  Comparison.ofRats ((2793380 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20403123 : Rat) / (5000000 : Rat))))))) .lt,
  -- P147.upper; P147: lambda=263/200, y=45/32: 2793380/10000000 < L_minus(1+(263/200)/(20403123/5000000)); L_plus(1+(263/200)/(20403121/5000000)) < 2793385/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((20403121 : Rat) / (5000000 : Rat))))))) ((2793385 : Rat)/10000000) .lt,
  -- P148.lower; P148: lambda=263/200, y=93/64: 2681147/10000000 < L_minus(1+(263/200)/(42764579/10000000)); L_plus(1+(263/200)/(21382287/5000000)) < 2681152/10000000.
  Comparison.ofRats ((2681147 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((42764579 : Rat) / (10000000 : Rat))))))) .lt,
  -- P148.upper; P148: lambda=263/200, y=93/64: 2681147/10000000 < L_minus(1+(263/200)/(42764579/10000000)); L_plus(1+(263/200)/(21382287/5000000)) < 2681152/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((21382287 : Rat) / (5000000 : Rat))))))) ((2681152 : Rat)/10000000) .lt,
  -- P149.lower; P149: lambda=263/200, y=3/2: 2572866/10000000 < L_minus(1+(263/200)/(22408447/5000000)); L_plus(1+(263/200)/(44816889/10000000)) < 2572871/10000000.
  Comparison.ofRats ((2572866 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((22408447 : Rat) / (5000000 : Rat))))))) .lt,
  -- P149.upper; P149: lambda=263/200, y=3/2: 2572866/10000000 < L_minus(1+(263/200)/(22408447/5000000)); L_plus(1+(263/200)/(44816889/10000000)) < 2572871/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((44816889 : Rat) / (10000000 : Rat))))))) ((2572871 : Rat)/10000000) .lt,
  -- P150.lower; P150: lambda=263/200, y=99/64: 2468439/10000000 < L_minus(1+(263/200)/(23483851/5000000)); L_plus(1+(263/200)/(46967697/10000000)) < 2468444/10000000.
  Comparison.ofRats ((2468439 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((23483851 : Rat) / (5000000 : Rat))))))) .lt,
  -- P150.upper; P150: lambda=263/200, y=99/64: 2468439/10000000 < L_minus(1+(263/200)/(23483851/5000000)); L_plus(1+(263/200)/(46967697/10000000)) < 2468444/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((46967697 : Rat) / (10000000 : Rat))))))) ((2468444 : Rat)/10000000) .lt,
  -- P151.lower; P151: lambda=263/200, y=51/32: 2367766/10000000 < L_minus(1+(263/200)/(4922173/1000000)); L_plus(1+(263/200)/(12305431/2500000)) < 2367772/10000000.
  Comparison.ofRats ((2367766 : Rat)/10000000) ((logLower (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((4922173 : Rat) / (1000000 : Rat))))))) .lt,
  -- P151.upper; P151: lambda=263/200, y=51/32: 2367766/10000000 < L_minus(1+(263/200)/(4922173/1000000)); L_plus(1+(263/200)/(12305431/2500000)) < 2367772/10000000.
  Comparison.ofRats ((logUpper (((1 : Rat) + (((263 : Rat) / (200 : Rat)) / ((12305431 : Rat) / (2500000 : Rat))))))) ((2367772 : Rat)/10000000) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Strict042
