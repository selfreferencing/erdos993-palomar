module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality016

def records : List Comparison := [
  -- P241.lower.lambda; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p241.lam) .eq,
  -- P241.lower.exp; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats (((14413827 : Rat) / (5000000 : Rat))) (e099.hi) .eq,
  -- P241.upper.lambda; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p241.lam) .eq,
  -- P241.upper.exp; P241: lambda=7/3, y=847/800: 5929994/10000000 < L_minus(1+(7/3)/(14413827/5000000)); L_plus(1+(7/3)/(28827651/10000000)) < 5930000/10000000.
  Comparison.ofRats (((28827651 : Rat) / (10000000 : Rat))) (e099.lo) .eq,
  -- P242.lower.lambda; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p242.lam) .eq,
  -- P242.lower.exp; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P242.upper.lambda; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p242.lam) .eq,
  -- P242.upper.exp; P242: lambda=7/3, y=9/8: 5639048/10000000 < L_minus(1+(7/3)/(3080217/1000000)); L_plus(1+(7/3)/(30802167/10000000)) < 5639054/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P243.lower.lambda; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p243.lam) .eq,
  -- P243.lower.exp; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats (((261991 : Rat) / (78125 : Rat))) (e107.hi) .eq,
  -- P243.upper.lambda; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p243.lam) .eq,
  -- P243.upper.exp; P243: lambda=7/3, y=121/100: 5281506/10000000 < L_minus(1+(7/3)/(261991/78125)); L_plus(1+(7/3)/(6706969/2000000)) < 5281511/10000000.
  Comparison.ofRats (((6706969 : Rat) / (2000000 : Rat))) (e107.lo) .eq,
  -- P244.lower.lambda; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p244.lam) .eq,
  -- P244.lower.exp; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P244.upper.lambda; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p244.lam) .eq,
  -- P244.upper.exp; P244: lambda=7/3, y=21/16: 4873570/10000000 < L_minus(1+(7/3)/(37154509/10000000)); L_plus(1+(7/3)/(18577253/5000000)) < 4873575/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P245.lower.lambda; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p245.lam) .eq,
  -- P245.lower.exp; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P245.upper.lambda; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p245.lam) .eq,
  -- P245.upper.exp; P245: lambda=7/3, y=3/2: 4191291/10000000 < L_minus(1+(7/3)/(22408447/5000000)); L_plus(1+(7/3)/(44816889/10000000)) < 4191296/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P246.lower.lambda; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p246.lam) .eq,
  -- P246.lower.exp; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P246.upper.lambda; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p246.lam) .eq,
  -- P246.upper.exp; P246: lambda=7/3, y=27/16: 3588086/10000000 < L_minus(1+(7/3)/(6757437/1250000)); L_plus(1+(7/3)/(1689359/312500)) < 3588092/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq,
  -- P247.lower.lambda; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p247.lam) .eq,
  -- P247.lower.exp; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P247.upper.lambda; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p247.lam) .eq,
  -- P247.upper.exp; P247: lambda=7/3, y=15/8: 3058862/10000000 < L_minus(1+(7/3)/(32604103/5000000)); L_plus(1+(7/3)/(6520819/1000000)) < 3058868/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P248.lower.lambda; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p248.lam) .eq,
  -- P248.lower.exp; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats (((629249 : Rat) / (80000 : Rat))) (e134.hi) .eq,
  -- P248.upper.lambda; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p248.lam) .eq,
  -- P248.upper.exp; P248: lambda=7/3, y=33/16: 2597837/10000000 < L_minus(1+(7/3)/(629249/80000)); L_plus(1+(7/3)/(78656091/10000000)) < 2597843/10000000.
  Comparison.ofRats (((78656091 : Rat) / (10000000 : Rat))) (e134.lo) .eq,
  -- P249.lower.lambda; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p249.lam) .eq,
  -- P249.lower.exp; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P249.upper.lambda; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p249.lam) .eq,
  -- P249.upper.exp; P249: lambda=7/3, y=9/4: 2198831/10000000 < L_minus(1+(7/3)/(23719357/2500000)); L_plus(1+(7/3)/(94877357/10000000)) < 2198836/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P250.lower.lambda; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p250.lam) .eq,
  -- P250.lower.exp; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats (((27609207 : Rat) / (2000000 : Rat))) (e138.hi) .eq,
  -- P250.upper.lambda; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p250.lam) .eq,
  -- P250.upper.exp; P250: lambda=7/3, y=21/8: 1561705/10000000 < L_minus(1+(7/3)/(27609207/2000000)); L_plus(1+(7/3)/(6902287/500000)) < 1561712/10000000.
  Comparison.ofRats (((6902287 : Rat) / (500000 : Rat))) (e138.lo) .eq,
  -- P251.lower.lambda; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p251.lam) .eq,
  -- P251.lower.exp; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P251.upper.lambda; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p251.lam) .eq,
  -- P251.upper.exp; P251: lambda=7/3, y=3: 1099023/10000000 < L_minus(1+(7/3)/(100428229/5000000)); L_plus(1+(7/3)/(40171073/2000000)) < 1099032/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 44 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality016
