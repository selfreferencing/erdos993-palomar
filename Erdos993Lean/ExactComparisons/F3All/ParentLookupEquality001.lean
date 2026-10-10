module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality001

def records : List Comparison := [
  -- P001.lower.lambda; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p001.lam) .eq,
  -- P001.lower.exp; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats (((10982853 : Rat) / (10000000 : Rat))) (e002.hi) .eq,
  -- P001.upper.lambda; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p001.lam) .eq,
  -- P001.upper.exp; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats (((219657 : Rat) / (200000 : Rat))) (e002.lo) .eq,
  -- P002.lower.lambda; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p002.lam) .eq,
  -- P002.lower.exp; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats (((376947 : Rat) / (312500 : Rat))) (e004.hi) .eq,
  -- P002.upper.lambda; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p002.lam) .eq,
  -- P002.upper.exp; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats (((12062301 : Rat) / (10000000 : Rat))) (e004.lo) .eq,
  -- P003.lower.lambda; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p003.lam) .eq,
  -- P003.lower.exp; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats (((6320593 : Rat) / (5000000 : Rat))) (e006.hi) .eq,
  -- P003.upper.lambda; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p003.lam) .eq,
  -- P003.upper.exp; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats (((12641183 : Rat) / (10000000 : Rat))) (e006.lo) .eq,
  -- P004.lower.lambda; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p004.lam) .eq,
  -- P004.lower.exp; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats (((13247849 : Rat) / (10000000 : Rat))) (e008.hi) .eq,
  -- P004.upper.lambda; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p004.lam) .eq,
  -- P004.upper.exp; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats (((6623923 : Rat) / (5000000 : Rat))) (e008.lo) .eq,
  -- P005.lower.lambda; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p005.lam) .eq,
  -- P005.lower.exp; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats (((3637479 : Rat) / (2500000 : Rat))) (e013.hi) .eq,
  -- P005.upper.lambda; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p005.lam) .eq,
  -- P005.upper.exp; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats (((14549913 : Rat) / (10000000 : Rat))) (e013.lo) .eq,
  -- P006.lower.lambda; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p006.lam) .eq,
  -- P006.lower.exp; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats (((3994989 : Rat) / (2500000 : Rat))) (e019.hi) .eq,
  -- P006.upper.lambda; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p006.lam) .eq,
  -- P006.upper.exp; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats (((15979953 : Rat) / (10000000 : Rat))) (e019.lo) .eq,
  -- P007.lower.lambda; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p007.lam) .eq,
  -- P007.lower.exp; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats (((4387637 : Rat) / (2500000 : Rat))) (e029.hi) .eq,
  -- P007.upper.lambda; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p007.lam) .eq,
  -- P007.upper.exp; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats (((3510109 : Rat) / (2000000 : Rat))) (e029.lo) .eq,
  -- P008.lower.lambda; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p008.lam) .eq,
  -- P008.lower.exp; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats (((10585001 : Rat) / (5000000 : Rat))) (e053.hi) .eq,
  -- P008.upper.lambda; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p008.lam) .eq,
  -- P008.upper.exp; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats (((21169999 : Rat) / (10000000 : Rat))) (e053.lo) .eq,
  -- P009.lower.lambda; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p009.lam) .eq,
  -- P009.lower.exp; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats (((3191987 : Rat) / (1250000 : Rat))) (e088.hi) .eq,
  -- P009.upper.lambda; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p009.lam) .eq,
  -- P009.upper.exp; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats (((25535893 : Rat) / (10000000 : Rat))) (e088.lo) .eq,
  -- P010.lower.lambda; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p010.lam) .eq,
  -- P010.lower.exp; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats (((3080217 : Rat) / (1000000 : Rat))) (e103.hi) .eq,
  -- P010.upper.lambda; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p010.lam) .eq,
  -- P010.upper.exp; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats (((30802167 : Rat) / (10000000 : Rat))) (e103.lo) .eq,
  -- P011.lower.lambda; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p011.lam) .eq,
  -- P011.lower.exp; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats (((37154509 : Rat) / (10000000 : Rat))) (e112.hi) .eq,
  -- P011.upper.lambda; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p011.lam) .eq,
  -- P011.upper.exp; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats (((18577253 : Rat) / (5000000 : Rat))) (e112.lo) .eq,
  -- P012.lower.lambda; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p012.lam) .eq,
  -- P012.lower.exp; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats (((22408447 : Rat) / (5000000 : Rat))) (e120.hi) .eq,
  -- P012.upper.lambda; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p012.lam) .eq,
  -- P012.upper.exp; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats (((44816889 : Rat) / (10000000 : Rat))) (e120.lo) .eq,
  -- P013.lower.lambda; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p013.lam) .eq,
  -- P013.lower.exp; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats (((32604103 : Rat) / (5000000 : Rat))) (e130.hi) .eq,
  -- P013.upper.lambda; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p013.lam) .eq,
  -- P013.upper.exp; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats (((6520819 : Rat) / (1000000 : Rat))) (e130.lo) .eq,
  -- P014.lower.lambda; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p014.lam) .eq,
  -- P014.lower.exp; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats (((23719357 : Rat) / (2500000 : Rat))) (e136.hi) .eq,
  -- P014.upper.lambda; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p014.lam) .eq,
  -- P014.upper.exp; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats (((94877357 : Rat) / (10000000 : Rat))) (e136.lo) .eq,
  -- P015.lower.lambda; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p015.lam) .eq,
  -- P015.lower.exp; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats (((100428229 : Rat) / (5000000 : Rat))) (e140.hi) .eq,
  -- P015.upper.lambda; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats (((1 : Rat) / (3 : Rat))) (p015.lam) .eq,
  -- P015.upper.exp; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats (((40171073 : Rat) / (2000000 : Rat))) (e140.lo) .eq,
  -- P016.lower.lambda; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p016.lam) .eq,
  -- P016.lower.exp; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats (((10982853 : Rat) / (10000000 : Rat))) (e002.hi) .eq,
  -- P016.upper.lambda; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats (((3 : Rat) / (5 : Rat))) (p016.lam) .eq,
  -- P016.upper.exp; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats (((219657 : Rat) / (200000 : Rat))) (e002.lo) .eq
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.ParentLookupEquality001
