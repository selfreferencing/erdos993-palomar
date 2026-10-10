module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012

def records : List Comparison := [
  -- P177.lower.lambda; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p177.lam) .eq,
  -- P177.lower.exp; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P177.upper.lambda; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p177.lam) .eq,
  -- P177.upper.exp; P177: lambda=3/2, y=27/16: 2448829/10000000 < L_minus(1+(3/2)/(6757437/1250000)); L_plus(1+(3/2)/(1689359/312500)) < 2448834/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq,
  -- P178.lower.lambda; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p178.lam) .eq,
  -- P178.lower.exp; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P178.upper.lambda; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p178.lam) .eq,
  -- P178.upper.exp; P178: lambda=3/2, y=15/8: 2070403/10000000 < L_minus(1+(3/2)/(32604103/5000000)); L_plus(1+(3/2)/(6520819/1000000)) < 2070407/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P179.lower.lambda; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p179.lam) .eq,
  -- P179.lower.exp; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats (((629249 : Rat) / (80000 : Rat))) (e134.hi) .eq,
  -- P179.upper.lambda; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p179.lam) .eq,
  -- P179.upper.exp; P179: lambda=3/2, y=33/16: 1745442/10000000 < L_minus(1+(3/2)/(629249/80000)); L_plus(1+(3/2)/(78656091/10000000)) < 1745445/10000000.
  Comparison.ofRats (((78656091 : Rat) / (10000000 : Rat))) (e134.lo) .eq,
  -- P180.lower.lambda; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p180.lam) .eq,
  -- P180.lower.exp; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P180.upper.lambda; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p180.lam) .eq,
  -- P180.upper.exp; P180: lambda=3/2, y=9/4: 1467795/10000000 < L_minus(1+(3/2)/(23719357/2500000)); L_plus(1+(3/2)/(94877357/10000000)) < 1467799/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P181.lower.lambda; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p181.lam) .eq,
  -- P181.lower.exp; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats (((27609207 : Rat) / (2000000 : Rat))) (e138.hi) .eq,
  -- P181.upper.lambda; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p181.lam) .eq,
  -- P181.upper.exp; P181: lambda=3/2, y=21/8: 1031514/10000000 < L_minus(1+(3/2)/(27609207/2000000)); L_plus(1+(3/2)/(6902287/500000)) < 1031519/10000000.
  Comparison.ofRats (((6902287 : Rat) / (500000 : Rat))) (e138.lo) .eq,
  -- P182.lower.lambda; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p182.lam) .eq,
  -- P182.lower.exp; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P182.upper.lambda; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats (((3 : Rat) / (2 : Rat))) (p182.lam) .eq,
  -- P182.upper.exp; P182: lambda=3/2, y=3: 720230/10000000 < L_minus(1+(3/2)/(100428229/5000000)); L_plus(1+(3/2)/(40171073/2000000)) < 720237/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P183.lower.lambda; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p183.lam) .eq,
  -- P183.lower.exp; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P183.upper.lambda; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p183.lam) .eq,
  -- P183.upper.exp; P183: lambda=7/4, y=3/8: 7897087/10000000 < L_minus(1+(7/4)/(3637479/2500000)); L_plus(1+(7/4)/(14549913/10000000)) < 7897096/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq,
  -- P184.lower.lambda; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p184.lam) .eq,
  -- P184.lower.exp; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats (((16652913 : Rat) / (10000000 : Rat))) (e023.hi) .eq,
  -- P184.upper.lambda; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p184.lam) .eq,
  -- P184.upper.exp; P184: lambda=7/4, y=51/100: 7182621/10000000 < L_minus(1+(7/4)/(16652913/10000000)); L_plus(1+(7/4)/(1665291/1000000)) < 7182630/10000000.
  Comparison.ofRats (((1665291 : Rat) / (1000000 : Rat))) (e023.lo) .eq,
  -- P185.lower.lambda; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p185.lam) .eq,
  -- P185.lower.exp; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P185.upper.lambda; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p185.lam) .eq,
  -- P185.upper.exp; P185: lambda=7/4, y=9/16: 6917055/10000000 < L_minus(1+(7/4)/(4387637/2500000)); L_plus(1+(7/4)/(3510109/2000000)) < 6917064/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P186.lower.lambda; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p186.lam) .eq,
  -- P186.lower.exp; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats (((18917457 : Rat) / (10000000 : Rat))) (e038.hi) .eq,
  -- P186.upper.lambda; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p186.lam) .eq,
  -- P186.upper.exp; P186: lambda=7/4, y=51/80: 6549627/10000000 < L_minus(1+(7/4)/(18917457/10000000)); L_plus(1+(7/4)/(9458727/5000000)) < 6549634/10000000.
  Comparison.ofRats (((9458727 : Rat) / (5000000 : Rat))) (e038.lo) .eq,
  -- P187.lower.lambda; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p187.lam) .eq,
  -- P187.lower.exp; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P187.upper.lambda; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p187.lam) .eq,
  -- P187.upper.exp; P187: lambda=7/4, y=3/4: 6024787/10000000 < L_minus(1+(7/4)/(10585001/5000000)); L_plus(1+(7/4)/(21169999/10000000)) < 6024793/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P188.lower.lambda; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p188.lam) .eq,
  -- P188.lower.exp; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats (((4297989 : Rat) / (2000000 : Rat))) (e056.hi) .eq,
  -- P188.upper.lambda; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p188.lam) .eq,
  -- P188.upper.exp; P188: lambda=7/4, y=153/200: 5957184/10000000 < L_minus(1+(7/4)/(4297989/2000000)); L_plus(1+(7/4)/(10744971/5000000)) < 5957189/10000000.
  Comparison.ofRats (((10744971 : Rat) / (5000000 : Rat))) (e056.lo) .eq,
  -- P189.lower.lambda; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p189.lam) .eq,
  -- P189.lower.exp; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats (((1145227 : Rat) / (500000 : Rat))) (e067.hi) .eq,
  -- P189.upper.lambda; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p189.lam) .eq,
  -- P189.upper.exp; P189: lambda=7/4, y=663/800: 5676067/10000000 < L_minus(1+(7/4)/(1145227/500000)); L_plus(1+(7/4)/(22904537/10000000)) < 5676073/10000000.
  Comparison.ofRats (((22904537 : Rat) / (10000000 : Rat))) (e067.lo) .eq,
  -- P190.lower.lambda; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p190.lam) .eq,
  -- P190.lower.exp; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats (((6103063 : Rat) / (2500000 : Rat))) (e082.hi) .eq,
  -- P190.upper.lambda; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p190.lam) .eq,
  -- P190.upper.exp; P190: lambda=7/4, y=357/400: 5404928/10000000 < L_minus(1+(7/4)/(6103063/2500000)); L_plus(1+(7/4)/(24412249/10000000)) < 5404934/10000000.
  Comparison.ofRats (((24412249 : Rat) / (10000000 : Rat))) (e082.lo) .eq,
  -- P191.lower.lambda; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p191.lam) .eq,
  -- P191.lower.exp; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P191.upper.lambda; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p191.lam) .eq,
  -- P191.upper.exp; P191: lambda=7/4, y=15/16: 5219492/10000000 < L_minus(1+(7/4)/(3191987/1250000)); L_plus(1+(7/4)/(25535893/10000000)) < 5219497/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P192.lower.lambda; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p192.lam) .eq,
  -- P192.lower.exp; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats (((27731949 : Rat) / (10000000 : Rat))) (e095.hi) .eq,
  -- P192.upper.lambda; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p192.lam) .eq,
  -- P192.upper.exp; P192: lambda=7/4, y=51/50: 4892183/10000000 < L_minus(1+(7/4)/(27731949/10000000)); L_plus(1+(7/4)/(13865973/5000000)) < 4892188/10000000.
  Comparison.ofRats (((13865973 : Rat) / (5000000 : Rat))) (e095.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality012
