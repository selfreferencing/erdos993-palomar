module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization007

def records : List Comparison := [
  -- P236.normalization; P236: lambda=7/3, y=363/400: 6634986/10000000 < L_minus(1+(7/3)/(6195299/2500000)); L_plus(1+(7/3)/(24781193/10000000)) < 6634994/10000000.
  Comparison.ofRats ((0 : Rat)) (p236.lo) .lt,
  -- P237.normalization; P237: lambda=7/3, y=5929/6400: 6543746/10000000 < L_minus(1+(7/3)/(25254173/10000000)); L_plus(1+(7/3)/(2525417/1000000)) < 6543753/10000000.
  Comparison.ofRats ((0 : Rat)) (p237.lo) .lt,
  -- P238.normalization; P238: lambda=7/3, y=121/128: 6453398/10000000 < L_minus(1+(7/3)/(25736177/10000000)); L_plus(1+(7/3)/(12868087/5000000)) < 6453405/10000000.
  Comparison.ofRats ((0 : Rat)) (p238.lo) .lt,
  -- P239.normalization; P239: lambda=7/3, y=1573/1600: 6275376/10000000 < L_minus(1+(7/3)/(13363979/5000000)); L_plus(1+(7/3)/(5345591/2000000)) < 6275382/10000000.
  Comparison.ofRats ((0 : Rat)) (p239.lo) .lt,
  -- P240.normalization; P240: lambda=7/3, y=3267/3200: 6100912/10000000 < L_minus(1+(7/3)/(693949/250000)); L_plus(1+(7/3)/(27757957/10000000)) < 6100917/10000000.
  Comparison.ofRats ((0 : Rat)) (p240.lo) .lt,
  -- P241.normalization; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats ((0 : Rat)) (p241.lo) .lt,
  -- P242.normalization; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats ((0 : Rat)) (p242.lo) .lt,
  -- P243.normalization; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats ((0 : Rat)) (p243.lo) .lt,
  -- P244.normalization; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats ((0 : Rat)) (p244.lo) .lt,
  -- P245.normalization; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats ((0 : Rat)) (p245.lo) .lt,
  -- P246.normalization; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats ((0 : Rat)) (p246.lo) .lt,
  -- P247.normalization; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats ((0 : Rat)) (p247.lo) .lt,
  -- P248.normalization; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats ((0 : Rat)) (p248.lo) .lt,
  -- P249.normalization; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats ((0 : Rat)) (p249.lo) .lt,
  -- P250.normalization; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats ((0 : Rat)) (p250.lo) .lt,
  -- P251.normalization; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats ((0 : Rat)) (p251.lo) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 16 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization007
