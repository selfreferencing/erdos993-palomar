module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002

def records : List Comparison := [
  -- P017.lower.lambda; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p017.lam) .eq,
  -- P017.lower.exp; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats (((376947 : Rat) / (312500 : Rat))) (e004.hi) .eq,
  -- P017.upper.lambda; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p017.lam) .eq,
  -- P017.upper.exp; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats (((12062301 : Rat) / (10000000 : Rat))) (e004.lo) .eq,
  -- P018.lower.lambda; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p018.lam) .eq,
  -- P018.lower.exp; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats (((6320593 : Rat) / (5000000 : Rat))) (e006.hi) .eq,
  -- P018.upper.lambda; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p018.lam) .eq,
  -- P018.upper.exp; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats (((12641183 : Rat) / (10000000 : Rat))) (e006.lo) .eq,
  -- P019.lower.lambda; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p019.lam) .eq,
  -- P019.lower.exp; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats (((13247849 : Rat) / (10000000 : Rat))) (e008.hi) .eq,
  -- P019.upper.lambda; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p019.lam) .eq,
  -- P019.upper.exp; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats (((6623923 : Rat) / (5000000 : Rat))) (e008.lo) .eq,
  -- P020.lower.lambda; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p020.lam) .eq,
  -- P020.lower.exp; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats (((13883627 : Rat) / (10000000 : Rat))) (e011.hi) .eq,
  -- P020.upper.lambda; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p020.lam) .eq,
  -- P020.upper.exp; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats (((1735453 : Rat) / (1250000 : Rat))) (e011.lo) .eq,
  -- P021.lower.lambda; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p021.lam) .eq,
  -- P021.lower.exp; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P021.upper.lambda; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p021.lam) .eq,
  -- P021.upper.exp; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq,
  -- P022.lower.lambda; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p022.lam) .eq,
  -- P022.lower.exp; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats (((15248181 : Rat) / (10000000 : Rat))) (e016.hi) .eq,
  -- P022.upper.lambda; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p022.lam) .eq,
  -- P022.upper.exp; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats (((7624089 : Rat) / (5000000 : Rat))) (e016.lo) .eq,
  -- P023.lower.lambda; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p023.lam) .eq,
  -- P023.lower.exp; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats (((3994989 : Rat) / (2500000 : Rat))) (e019.hi) .eq,
  -- P023.upper.lambda; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p023.lam) .eq,
  -- P023.upper.exp; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats (((15979953 : Rat) / (10000000 : Rat))) (e019.lo) .eq,
  -- P024.lower.lambda; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p024.lam) .eq,
  -- P024.lower.exp; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P024.upper.lambda; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p024.lam) .eq,
  -- P024.upper.exp; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P025.lower.lambda; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p025.lam) .eq,
  -- P025.lower.exp; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats (((9637753 : Rat) / (5000000 : Rat))) (e040.hi) .eq,
  -- P025.upper.lambda; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p025.lam) .eq,
  -- P025.upper.exp; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats (((19275503 : Rat) / (10000000 : Rat))) (e040.lo) .eq,
  -- P026.lower.lambda; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p026.lam) .eq,
  -- P026.lower.exp; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P026.upper.lambda; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p026.lam) .eq,
  -- P026.upper.exp; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P027.lower.lambda; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p027.lam) .eq,
  -- P027.lower.exp; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats (((11625349 : Rat) / (5000000 : Rat))) (e071.hi) .eq,
  -- P027.upper.lambda; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p027.lam) .eq,
  -- P027.upper.exp; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats (((4650139 : Rat) / (2000000 : Rat))) (e071.lo) .eq,
  -- P028.lower.lambda; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p028.lam) .eq,
  -- P028.lower.exp; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P028.upper.lambda; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p028.lam) .eq,
  -- P028.upper.exp; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P029.lower.lambda; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p029.lam) .eq,
  -- P029.lower.exp; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P029.upper.lambda; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p029.lam) .eq,
  -- P029.upper.exp; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P030.lower.lambda; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p030.lam) .eq,
  -- P030.lower.exp; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P030.upper.lambda; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p030.lam) .eq,
  -- P030.upper.exp; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P031.lower.lambda; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p031.lam) .eq,
  -- P031.lower.exp; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P031.upper.lambda; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p031.lam) .eq,
  -- P031.upper.exp; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P032.lower.lambda; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p032.lam) .eq,
  -- P032.lower.exp; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats (((6757437 : Rat) / (1250000 : Rat))) (e126.hi) .eq,
  -- P032.upper.lambda; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p032.lam) .eq,
  -- P032.upper.exp; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats (((1689359 : Rat) / (312500 : Rat))) (e126.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality002
