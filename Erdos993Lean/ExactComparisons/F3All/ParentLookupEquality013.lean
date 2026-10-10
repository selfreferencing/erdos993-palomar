module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality013

def records : List Comparison := [
  -- P193.lower.lambda; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p193.lam) .eq,
  -- P193.lower.exp; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P193.upper.lambda; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p193.lam) .eq,
  -- P193.upper.exp; P193: lambda=7/4, y=9/8: 4498911/10000000 < L_minus(1+(7/4)/(3080217/1000000)); L_plus(1+(7/4)/(30802167/10000000)) < 4498916/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P194.lower.lambda; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p194.lam) .eq,
  -- P194.lower.exp; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P194.upper.lambda; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p194.lam) .eq,
  -- P194.upper.exp; P194: lambda=7/4, y=21/16: 3859463/10000000 < L_minus(1+(7/4)/(37154509/10000000)); L_plus(1+(7/4)/(18577253/5000000)) < 3859468/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P195.lower.lambda; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p195.lam) .eq,
  -- P195.lower.exp; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P195.upper.lambda; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p195.lam) .eq,
  -- P195.upper.exp; P195: lambda=7/4, y=3/2: 3296471/10000000 < L_minus(1+(7/4)/(22408447/5000000)); L_plus(1+(7/4)/(44816889/10000000)) < 3296476/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P196.lower.lambda; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p196.lam) .eq,
  -- P196.lower.exp; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P196.upper.lambda; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p196.lam) .eq,
  -- P196.upper.exp; P196: lambda=7/4, y=27/16: 2804437/10000000 < L_minus(1+(7/4)/(6757437/1250000)); L_plus(1+(7/4)/(1689359/312500)) < 2804442/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq,
  -- P197.lower.lambda; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p197.lam) .eq,
  -- P197.lower.exp; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P197.upper.lambda; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p197.lam) .eq,
  -- P197.upper.exp; P197: lambda=7/4, y=15/8: 2377332/10000000 < L_minus(1+(7/4)/(32604103/5000000)); L_plus(1+(7/4)/(6520819/1000000)) < 2377338/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P198.lower.lambda; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p198.lam) .eq,
  -- P198.lower.exp; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats (((629249 : Rat) / (80000 : Rat))) (e134.hi) .eq,
  -- P198.upper.lambda; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p198.lam) .eq,
  -- P198.upper.exp; P198: lambda=7/4, y=33/16: 2008875/10000000 < L_minus(1+(7/4)/(629249/80000)); L_plus(1+(7/4)/(78656091/10000000)) < 2008879/10000000.
  Comparison.ofRats (((78656091 : Rat) / (10000000 : Rat))) (e134.lo) .eq,
  -- P199.lower.lambda; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p199.lam) .eq,
  -- P199.lower.exp; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P199.upper.lambda; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p199.lam) .eq,
  -- P199.upper.exp; P199: lambda=7/4, y=9/4: 1692771/10000000 < L_minus(1+(7/4)/(23719357/2500000)); L_plus(1+(7/4)/(94877357/10000000)) < 1692775/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P200.lower.lambda; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p200.lam) .eq,
  -- P200.lower.exp; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats (((27609207 : Rat) / (2000000 : Rat))) (e138.hi) .eq,
  -- P200.upper.lambda; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p200.lam) .eq,
  -- P200.upper.exp; P200: lambda=7/4, y=21/8: 1193544/10000000 < L_minus(1+(7/4)/(27609207/2000000)); L_plus(1+(7/4)/(6902287/500000)) < 1193549/10000000.
  Comparison.ofRats (((6902287 : Rat) / (500000 : Rat))) (e138.lo) .eq,
  -- P201.lower.lambda; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p201.lam) .eq,
  -- P201.lower.exp; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P201.upper.lambda; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats (((7 : Rat) / (4 : Rat))) (p201.lam) .eq,
  -- P201.upper.exp; P201: lambda=7/4, y=3: 835382/10000000 < L_minus(1+(7/4)/(100428229/5000000)); L_plus(1+(7/4)/(40171073/2000000)) < 835389/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P202.lower.lambda; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats ((2 : Rat)) (p202.lam) .eq,
  -- P202.lower.exp; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P202.upper.lambda; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats ((2 : Rat)) (p202.lam) .eq,
  -- P202.upper.exp; P202: lambda=2, y=3/8: 8648193/10000000 < L_minus(1+(2)/(3637479/2500000)); L_plus(1+(2)/(14549913/10000000)) < 8648202/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq,
  -- P203.lower.lambda; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats ((2 : Rat)) (p203.lam) .eq,
  -- P203.lower.exp; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats (((4333133 : Rat) / (2500000 : Rat))) (e027.hi) .eq,
  -- P203.upper.lambda; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats ((2 : Rat)) (p203.lam) .eq,
  -- P203.upper.exp; P203: lambda=2, y=11/20: 7672793/10000000 < L_minus(1+(2)/(4333133/2500000)); L_plus(1+(2)/(17332529/10000000)) < 7672802/10000000.
  Comparison.ofRats (((17332529 : Rat) / (10000000 : Rat))) (e027.lo) .eq,
  -- P204.lower.lambda; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats ((2 : Rat)) (p204.lam) .eq,
  -- P204.lower.exp; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P204.upper.lambda; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats ((2 : Rat)) (p204.lam) .eq,
  -- P204.upper.exp; P204: lambda=2, y=9/16: 7606022/10000000 < L_minus(1+(2)/(4387637/2500000)); L_plus(1+(2)/(3510109/2000000)) < 7606031/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P205.lower.lambda; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats ((2 : Rat)) (p205.lam) .eq,
  -- P205.lower.exp; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats (((1242961 : Rat) / (625000 : Rat))) (e044.hi) .eq,
  -- P205.upper.lambda; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats ((2 : Rat)) (p205.lam) .eq,
  -- P205.upper.exp; P205: lambda=2, y=11/16: 6959741/10000000 < L_minus(1+(2)/(1242961/625000)); L_plus(1+(2)/(19887373/10000000)) < 6959750/10000000.
  Comparison.ofRats (((19887373 : Rat) / (10000000 : Rat))) (e044.lo) .eq,
  -- P206.lower.lambda; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats ((2 : Rat)) (p206.lam) .eq,
  -- P206.lower.exp; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P206.upper.lambda; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats ((2 : Rat)) (p206.lam) .eq,
  -- P206.upper.exp; P206: lambda=2, y=3/4: 6651243/10000000 < L_minus(1+(2)/(10585001/5000000)); L_plus(1+(2)/(21169999/10000000)) < 6651250/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P207.lower.lambda; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats ((2 : Rat)) (p207.lam) .eq,
  -- P207.lower.exp; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats (((21302729 : Rat) / (10000000 : Rat))) (e054.hi) .eq,
  -- P207.upper.lambda; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats ((2 : Rat)) (p207.lam) .eq,
  -- P207.upper.exp; P207: lambda=2, y=121/160: 6620930/10000000 < L_minus(1+(2)/(21302729/10000000)); L_plus(1+(2)/(10651363/5000000)) < 6620937/10000000.
  Comparison.ofRats (((10651363 : Rat) / (5000000 : Rat))) (e054.lo) .eq,
  -- P208.lower.lambda; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats ((2 : Rat)) (p208.lam) .eq,
  -- P208.lower.exp; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats (((22818809 : Rat) / (10000000 : Rat))) (e066.hi) .eq,
  -- P208.upper.lambda; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats ((2 : Rat)) (p208.lam) .eq,
  -- P208.upper.exp; P208: lambda=2, y=33/40: 6293920/10000000 < L_minus(1+(2)/(22818809/10000000)); L_plus(1+(2)/(11409403/5000000)) < 6293926/10000000.
  Comparison.ofRats (((11409403 : Rat) / (5000000 : Rat))) (e066.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality013
