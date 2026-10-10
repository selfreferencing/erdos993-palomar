module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004

def records : List Comparison := [
  -- P049.lower.lambda; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p049.lam) .eq,
  -- P049.lower.exp; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats (((11625349 : Rat) / (5000000 : Rat))) (e071.hi) .eq,
  -- P049.upper.lambda; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p049.lam) .eq,
  -- P049.upper.exp; P049: lambda=7/8, y=27/32: 3194223/10000000 < L_minus(1+(7/8)/(11625349/5000000)); L_plus(1+(7/8)/(4650139/2000000)) < 3194228/10000000.
  Comparison.ofRats (((4650139 : Rat) / (2000000 : Rat))) (e071.lo) .eq,
  -- P050.lower.lambda; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p050.lam) .eq,
  -- P050.lower.exp; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P050.upper.lambda; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p050.lam) .eq,
  -- P050.upper.exp; P050: lambda=7/8, y=15/16: 2946486/10000000 < L_minus(1+(7/8)/(3191987/1250000)); L_plus(1+(7/8)/(25535893/10000000)) < 2946492/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P051.lower.lambda; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p051.lam) .eq,
  -- P051.lower.exp; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats (((5609139 : Rat) / (2000000 : Rat))) (e097.hi) .eq,
  -- P051.upper.lambda; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p051.lam) .eq,
  -- P051.upper.exp; P051: lambda=7/8, y=33/32: 2715454/10000000 < L_minus(1+(7/8)/(5609139/2000000)); L_plus(1+(7/8)/(7011423/2500000)) < 2715459/10000000.
  Comparison.ofRats (((7011423 : Rat) / (2500000 : Rat))) (e097.lo) .eq,
  -- P052.lower.lambda; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p052.lam) .eq,
  -- P052.lower.exp; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P052.upper.lambda; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p052.lam) .eq,
  -- P052.upper.exp; P052: lambda=7/8, y=9/8: 2500351/10000000 < L_minus(1+(7/8)/(3080217/1000000)); L_plus(1+(7/8)/(30802167/10000000)) < 2500356/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P053.lower.lambda; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p053.lam) .eq,
  -- P053.lower.exp; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats (((16914783 : Rat) / (5000000 : Rat))) (e108.hi) .eq,
  -- P053.upper.lambda; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p053.lam) .eq,
  -- P053.upper.exp; P053: lambda=7/8, y=39/32: 2300390/10000000 < L_minus(1+(7/8)/(16914783/5000000)); L_plus(1+(7/8)/(16914781/5000000)) < 2300395/10000000.
  Comparison.ofRats (((16914781 : Rat) / (5000000 : Rat))) (e108.lo) .eq,
  -- P054.lower.lambda; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p054.lam) .eq,
  -- P054.lower.exp; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P054.upper.lambda; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p054.lam) .eq,
  -- P054.upper.exp; P054: lambda=7/8, y=21/16: 2114780/10000000 < L_minus(1+(7/8)/(37154509/10000000)); L_plus(1+(7/8)/(18577253/5000000)) < 2114784/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P055.lower.lambda; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p055.lam) .eq,
  -- P055.lower.exp; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats (((20403123 : Rat) / (5000000 : Rat))) (e116.hi) .eq,
  -- P055.upper.lambda; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p055.lam) .eq,
  -- P055.upper.exp; P055: lambda=7/8, y=45/32: 1942730/10000000 < L_minus(1+(7/8)/(20403123/5000000)); L_plus(1+(7/8)/(20403121/5000000)) < 1942733/10000000.
  Comparison.ofRats (((20403121 : Rat) / (5000000 : Rat))) (e116.lo) .eq,
  -- P056.lower.lambda; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p056.lam) .eq,
  -- P056.lower.exp; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P056.upper.lambda; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p056.lam) .eq,
  -- P056.upper.exp; P056: lambda=7/8, y=3/2: 1783459/10000000 < L_minus(1+(7/8)/(22408447/5000000)); L_plus(1+(7/8)/(44816889/10000000)) < 1783462/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P057.lower.lambda; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p057.lam) .eq,
  -- P057.lower.exp; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats (((4922173 : Rat) / (1000000 : Rat))) (e124.hi) .eq,
  -- P057.upper.lambda; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p057.lam) .eq,
  -- P057.upper.exp; P057: lambda=7/8, y=51/32: 1636201/10000000 < L_minus(1+(7/8)/(4922173/1000000)); L_plus(1+(7/8)/(12305431/2500000)) < 1636205/10000000.
  Comparison.ofRats (((12305431 : Rat) / (2500000 : Rat))) (e124.lo) .eq,
  -- P058.lower.lambda; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p058.lam) .eq,
  -- P058.lower.exp; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P058.upper.lambda; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p058.lam) .eq,
  -- P058.upper.exp; P058: lambda=7/8, y=27/16: 1500209/10000000 < L_minus(1+(7/8)/(6757437/1250000)); L_plus(1+(7/8)/(1689359/312500)) < 1500212/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq,
  -- P059.lower.lambda; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p059.lam) .eq,
  -- P059.lower.exp; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P059.upper.lambda; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p059.lam) .eq,
  -- P059.upper.exp; P059: lambda=7/8, y=15/8: 1259147/10000000 < L_minus(1+(7/8)/(32604103/5000000)); L_plus(1+(7/8)/(6520819/1000000)) < 1259150/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P060.lower.lambda; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p060.lam) .eq,
  -- P060.lower.exp; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats (((629249 : Rat) / (80000 : Rat))) (e134.hi) .eq,
  -- P060.upper.lambda; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p060.lam) .eq,
  -- P060.upper.exp; P060: lambda=7/8, y=33/16: 1054797/10000000 < L_minus(1+(7/8)/(629249/80000)); L_plus(1+(7/8)/(78656091/10000000)) < 1054801/10000000.
  Comparison.ofRats (((78656091 : Rat) / (10000000 : Rat))) (e134.lo) .eq,
  -- P061.lower.lambda; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p061.lam) .eq,
  -- P061.lower.exp; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P061.upper.lambda; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p061.lam) .eq,
  -- P061.upper.exp; P061: lambda=7/8, y=9/4: 882161/10000000 < L_minus(1+(7/8)/(23719357/2500000)); L_plus(1+(7/8)/(94877357/10000000)) < 882164/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P062.lower.lambda; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p062.lam) .eq,
  -- P062.lower.exp; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats (((27609207 : Rat) / (2000000 : Rat))) (e138.hi) .eq,
  -- P062.upper.lambda; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p062.lam) .eq,
  -- P062.upper.exp; P062: lambda=7/8, y=21/8: 614567/10000000 < L_minus(1+(7/8)/(27609207/2000000)); L_plus(1+(7/8)/(6902287/500000)) < 614572/10000000.
  Comparison.ofRats (((6902287 : Rat) / (500000 : Rat))) (e138.lo) .eq,
  -- P063.lower.lambda; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p063.lam) .eq,
  -- P063.lower.exp; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P063.upper.lambda; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats (((7 : Rat) / (8 : Rat))) (p063.lam) .eq,
  -- P063.upper.exp; P063: lambda=7/8, y=3: 426411/10000000 < L_minus(1+(7/8)/(100428229/5000000)); L_plus(1+(7/8)/(40171073/2000000)) < 426416/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P064.lower.lambda; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats (((28 : Rat) / (25 : Rat))) (p064.lam) .eq,
  -- P064.lower.exp; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats (((376947 : Rat) / (312500 : Rat))) (e004.hi) .eq,
  -- P064.upper.lambda; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats (((28 : Rat) / (25 : Rat))) (p064.lam) .eq,
  -- P064.upper.exp; P064: lambda=28/25, y=3/16: 6567486/10000000 < L_minus(1+(28/25)/(376947/312500)); L_plus(1+(28/25)/(12062301/10000000)) < 6567493/10000000.
  Comparison.ofRats (((12062301 : Rat) / (10000000 : Rat))) (e004.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality004
