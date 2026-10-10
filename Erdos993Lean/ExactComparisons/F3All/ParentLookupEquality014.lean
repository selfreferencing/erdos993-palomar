module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality014

def records : List Comparison := [
  -- P209.lower.lambda; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats ((2 : Rat)) (p209.lam) .eq,
  -- P209.lower.exp; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats (((23616843 : Rat) / (10000000 : Rat))) (e074.hi) .eq,
  -- P209.upper.lambda; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats ((2 : Rat)) (p209.lam) .eq,
  -- P209.upper.exp; P209: lambda=2, y=55/64: 6134829/10000000 < L_minus(1+(2)/(23616843/10000000)); L_plus(1+(2)/(590421/250000)) < 6134835/10000000.
  Comparison.ofRats (((590421 : Rat) / (250000 : Rat))) (e074.lo) .eq,
  -- P210.lower.lambda; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats ((2 : Rat)) (p210.lam) .eq,
  -- P210.lower.exp; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats (((24442787 : Rat) / (10000000 : Rat))) (e083.hi) .eq,
  -- P210.upper.lambda; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats ((2 : Rat)) (p210.lam) .eq,
  -- P210.upper.exp; P210: lambda=2, y=143/160: 5978672/10000000 < L_minus(1+(2)/(24442787/10000000)); L_plus(1+(2)/(763837/312500)) < 5978678/10000000.
  Comparison.ofRats (((763837 : Rat) / (312500 : Rat))) (e083.lo) .eq,
  -- P211.lower.lambda; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats ((2 : Rat)) (p211.lam) .eq,
  -- P211.lower.exp; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P211.upper.lambda; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats ((2 : Rat)) (p211.lam) .eq,
  -- P211.upper.exp; P211: lambda=2, y=15/16: 5784155/10000000 < L_minus(1+(2)/(3191987/1250000)); L_plus(1+(2)/(25535893/10000000)) < 5784161/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P212.lower.lambda; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats ((2 : Rat)) (p212.lam) .eq,
  -- P212.lower.exp; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats (((1309117 : Rat) / (500000 : Rat))) (e091.hi) .eq,
  -- P212.upper.lambda; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats ((2 : Rat)) (p212.lam) .eq,
  -- P212.upper.exp; P212: lambda=2, y=77/80: 5675121/10000000 < L_minus(1+(2)/(1309117/500000)); L_plus(1+(2)/(26182337/10000000)) < 5675126/10000000.
  Comparison.ofRats (((26182337 : Rat) / (10000000 : Rat))) (e091.lo) .eq,
  -- P213.lower.lambda; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats ((2 : Rat)) (p213.lam) .eq,
  -- P213.lower.exp; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats (((15020831 : Rat) / (5000000 : Rat))) (e101.hi) .eq,
  -- P213.upper.lambda; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats ((2 : Rat)) (p213.lam) .eq,
  -- P213.upper.exp; P213: lambda=2, y=11/10: 5102705/10000000 < L_minus(1+(2)/(15020831/5000000)); L_plus(1+(2)/(30041659/10000000)) < 5102710/10000000.
  Comparison.ofRats (((30041659 : Rat) / (10000000 : Rat))) (e101.lo) .eq,
  -- P214.lower.lambda; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats ((2 : Rat)) (p214.lam) .eq,
  -- P214.lower.exp; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P214.upper.lambda; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats ((2 : Rat)) (p214.lam) .eq,
  -- P214.upper.exp; P214: lambda=2, y=9/8: 5003537/10000000 < L_minus(1+(2)/(3080217/1000000)); L_plus(1+(2)/(30802167/10000000)) < 5003542/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P215.lower.lambda; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats ((2 : Rat)) (p215.lam) .eq,
  -- P215.lower.exp; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P215.upper.lambda; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats ((2 : Rat)) (p215.lam) .eq,
  -- P215.upper.exp; P215: lambda=2, y=21/16: 4306729/10000000 < L_minus(1+(2)/(37154509/10000000)); L_plus(1+(2)/(18577253/5000000)) < 4306734/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P216.lower.lambda; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats ((2 : Rat)) (p216.lam) .eq,
  -- P216.lower.exp; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P216.upper.lambda; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats ((2 : Rat)) (p216.lam) .eq,
  -- P216.upper.exp; P216: lambda=2, y=3/2: 3689808/10000000 < L_minus(1+(2)/(22408447/5000000)); L_plus(1+(2)/(44816889/10000000)) < 3689813/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P217.lower.lambda; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats ((2 : Rat)) (p217.lam) .eq,
  -- P217.lower.exp; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P217.upper.lambda; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats ((2 : Rat)) (p217.lam) .eq,
  -- P217.upper.exp; P217: lambda=2, y=27/16: 3147833/10000000 < L_minus(1+(2)/(6757437/1250000)); L_plus(1+(2)/(1689359/312500)) < 3147838/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq,
  -- P218.lower.lambda; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats ((2 : Rat)) (p218.lam) .eq,
  -- P218.lower.exp; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P218.upper.lambda; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats ((2 : Rat)) (p218.lam) .eq,
  -- P218.upper.exp; P218: lambda=2, y=15/8: 2675121/10000000 < L_minus(1+(2)/(32604103/5000000)); L_plus(1+(2)/(6520819/1000000)) < 2675127/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P219.lower.lambda; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats ((2 : Rat)) (p219.lam) .eq,
  -- P219.lower.exp; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats (((629249 : Rat) / (80000 : Rat))) (e134.hi) .eq,
  -- P219.upper.lambda; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats ((2 : Rat)) (p219.lam) .eq,
  -- P219.upper.exp; P219: lambda=2, y=33/16: 2265545/10000000 < L_minus(1+(2)/(629249/80000)); L_plus(1+(2)/(78656091/10000000)) < 2265551/10000000.
  Comparison.ofRats (((78656091 : Rat) / (10000000 : Rat))) (e134.lo) .eq,
  -- P220.lower.lambda; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats ((2 : Rat)) (p220.lam) .eq,
  -- P220.lower.exp; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P220.upper.lambda; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats ((2 : Rat)) (p220.lam) .eq,
  -- P220.upper.exp; P220: lambda=2, y=9/4: 1912797/10000000 < L_minus(1+(2)/(23719357/2500000)); L_plus(1+(2)/(94877357/10000000)) < 1912802/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P221.lower.lambda; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats ((2 : Rat)) (p221.lam) .eq,
  -- P221.lower.exp; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats (((27609207 : Rat) / (2000000 : Rat))) (e138.hi) .eq,
  -- P221.upper.lambda; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats ((2 : Rat)) (p221.lam) .eq,
  -- P221.upper.exp; P221: lambda=2, y=21/8: 1352990/10000000 < L_minus(1+(2)/(27609207/2000000)); L_plus(1+(2)/(6902287/500000)) < 1352996/10000000.
  Comparison.ofRats (((6902287 : Rat) / (500000 : Rat))) (e138.lo) .eq,
  -- P222.lower.lambda; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats ((2 : Rat)) (p222.lam) .eq,
  -- P222.lower.exp; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P222.upper.lambda; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats ((2 : Rat)) (p222.lam) .eq,
  -- P222.upper.exp; P222: lambda=2, y=3: 949223/10000000 < L_minus(1+(2)/(100428229/5000000)); L_plus(1+(2)/(40171073/2000000)) < 949231/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P223.lower.lambda; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p223.lam) .eq,
  -- P223.lower.exp; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats (((6766189 : Rat) / (5000000 : Rat))) (e009.hi) .eq,
  -- P223.upper.lambda; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p223.lam) .eq,
  -- P223.upper.exp; P223: lambda=7/3, y=121/400: 10021959/10000000 < L_minus(1+(7/3)/(6766189/5000000)); L_plus(1+(7/3)/(108259/80000)) < 10021971/10000000.
  Comparison.ofRats (((108259 : Rat) / (80000 : Rat))) (e009.lo) .eq,
  -- P224.lower.lambda; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p224.lam) .eq,
  -- P224.lower.exp; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P224.upper.lambda; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats (((7 : Rat) / (3 : Rat))) (p224.lam) .eq,
  -- P224.upper.exp; P224: lambda=7/3, y=3/8: 9569230/10000000 < L_minus(1+(7/3)/(3637479/2500000)); L_plus(1+(7/3)/(14549913/10000000)) < 9569242/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality014
