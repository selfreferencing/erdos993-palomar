module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization003

def records : List Comparison := [
  -- E129.normalization; E129: 62222089/10000000 < E_minus(117/64); E_plus(117/64) < 62222103/10000000.
  Comparison.ofRats ((1 : Rat)) (e129.lo) .le,
  -- E130.normalization; E130: 65208190/10000000 < E_minus(15/8); E_plus(15/8) < 65208206/10000000.
  Comparison.ofRats ((1 : Rat)) (e130.lo) .le,
  -- E131.normalization; E131: 68337596/10000000 < E_minus(123/64); E_plus(123/64) < 68337615/10000000.
  Comparison.ofRats ((1 : Rat)) (e131.lo) .le,
  -- E132.normalization; E132: 71617186/10000000 < E_minus(63/32); E_plus(63/32) < 71617209/10000000.
  Comparison.ofRats ((1 : Rat)) (e132.lo) .le,
  -- E133.normalization; E133: 75054166/10000000 < E_minus(129/64); E_plus(129/64) < 75054194/10000000.
  Comparison.ofRats ((1 : Rat)) (e133.lo) .le,
  -- E134.normalization; E134: 78656091/10000000 < E_minus(33/16); E_plus(33/16) < 78656125/10000000.
  Comparison.ofRats ((1 : Rat)) (e134.lo) .le,
  -- E135.normalization; E135: 86386816/10000000 < E_minus(69/32); E_plus(69/32) < 86386865/10000000.
  Comparison.ofRats ((1 : Rat)) (e135.lo) .le,
  -- E136.normalization; E136: 94877357/10000000 < E_minus(9/4); E_plus(9/4) < 94877428/10000000.
  Comparison.ofRats ((1 : Rat)) (e136.lo) .le,
  -- E137.normalization; E137: 114443938/10000000 < E_minus(39/16); E_plus(39/16) < 114444085/10000000.
  Comparison.ofRats ((1 : Rat)) (e137.lo) .le,
  -- E138.normalization; E138: 138045740/10000000 < E_minus(21/8); E_plus(21/8) < 138046035/10000000.
  Comparison.ofRats ((1 : Rat)) (e138.lo) .le,
  -- E139.normalization; E139: 166514947/10000000 < E_minus(45/16); E_plus(45/16) < 166515523/10000000.
  Comparison.ofRats ((1 : Rat)) (e139.lo) .le,
  -- E140.normalization; E140: 200855365/10000000 < E_minus(3); E_plus(3) < 200856458/10000000.
  Comparison.ofRats ((1 : Rat)) (e140.lo) .le,
  -- B01.normalization; B01: 2876818/10000000 < L_minus(1+(1/3)); L_plus(1+(1/3)) < 2876823/10000000.
  Comparison.ofRats ((0 : Rat)) (b01.lo) .lt,
  -- B02.normalization; B02: 4700034/10000000 < L_minus(1+(3/5)); L_plus(1+(3/5)) < 4700039/10000000.
  Comparison.ofRats ((0 : Rat)) (b02.lo) .lt,
  -- B03.normalization; B03: 6286083/10000000 < L_minus(1+(7/8)); L_plus(1+(7/8)) < 6286089/10000000.
  Comparison.ofRats ((0 : Rat)) (b03.lo) .lt,
  -- B04.normalization; B04: 7514155/10000000 < L_minus(1+(28/25)); L_plus(1+(28/25)) < 7514163/10000000.
  Comparison.ofRats ((0 : Rat)) (b04.lo) .lt,
  -- B05.normalization; B05: 8394091/10000000 < L_minus(1+(263/200)); L_plus(1+(263/200)) < 8394099/10000000.
  Comparison.ofRats ((0 : Rat)) (b05.lo) .lt,
  -- B06.normalization; B06: 9162900/10000000 < L_minus(1+(3/2)); L_plus(1+(3/2)) < 9162909/10000000.
  Comparison.ofRats ((0 : Rat)) (b06.lo) .lt,
  -- B07.normalization; B07: 10116001/10000000 < L_minus(1+(7/4)); L_plus(1+(7/4)) < 10116011/10000000.
  Comparison.ofRats ((0 : Rat)) (b07.lo) .lt,
  -- B08.normalization; B08: 10986116/10000000 < L_minus(1+(2)); L_plus(1+(2)) < 10986125/10000000.
  Comparison.ofRats ((0 : Rat)) (b08.lo) .lt,
  -- B09.normalization; B09: 12039721/10000000 < L_minus(1+(7/3)); L_plus(1+(7/3)) < 12039731/10000000.
  Comparison.ofRats ((0 : Rat)) (b09.lo) .lt,
  -- P001.normalization; P001: lambda=1/3, y=3/32: 2650553/10000000 < L_minus(1+(1/3)/(10982853/10000000)); L_plus(1+(1/3)/(219657/200000)) < 2650558/10000000.
  Comparison.ofRats ((0 : Rat)) (p001.lo) .lt,
  -- P002.normalization; P002: lambda=1/3, y=3/16: 2439987/10000000 < L_minus(1+(1/3)/(376947/312500)); L_plus(1+(1/3)/(12062301/10000000)) < 2439992/10000000.
  Comparison.ofRats ((0 : Rat)) (p002.lo) .lt,
  -- P003.normalization; P003: lambda=1/3, y=15/64: 2340344/10000000 < L_minus(1+(1/3)/(6320593/5000000)); L_plus(1+(1/3)/(12641183/10000000)) < 2340349/10000000.
  Comparison.ofRats ((0 : Rat)) (p003.lo) .lt,
  -- P004.normalization; P004: lambda=1/3, y=9/32: 2244330/10000000 < L_minus(1+(1/3)/(13247849/10000000)); L_plus(1+(1/3)/(6623923/5000000)) < 2244335/10000000.
  Comparison.ofRats ((0 : Rat)) (p004.lo) .lt,
  -- P005.normalization; P005: lambda=1/3, y=3/8: 2062791/10000000 < L_minus(1+(1/3)/(3637479/2500000)); L_plus(1+(1/3)/(14549913/10000000)) < 2062795/10000000.
  Comparison.ofRats ((0 : Rat)) (p005.lo) .lt,
  -- P006.normalization; P006: lambda=1/3, y=15/32: 1894581/10000000 < L_minus(1+(1/3)/(3994989/2500000)); L_plus(1+(1/3)/(15979953/10000000)) < 1894584/10000000.
  Comparison.ofRats ((0 : Rat)) (p006.lo) .lt,
  -- P007.normalization; P007: lambda=1/3, y=9/16: 1738923/10000000 < L_minus(1+(1/3)/(4387637/2500000)); L_plus(1+(1/3)/(3510109/2000000)) < 1738926/10000000.
  Comparison.ofRats ((0 : Rat)) (p007.lo) .lt,
  -- P008.normalization; P008: lambda=1/3, y=3/4: 1462239/10000000 < L_minus(1+(1/3)/(10585001/5000000)); L_plus(1+(1/3)/(21169999/10000000)) < 1462242/10000000.
  Comparison.ofRats ((0 : Rat)) (p008.lo) .lt,
  -- P009.normalization; P009: lambda=1/3, y=15/16: 1226910/10000000 < L_minus(1+(1/3)/(3191987/1250000)); L_plus(1+(1/3)/(25535893/10000000)) < 1226913/10000000.
  Comparison.ofRats ((0 : Rat)) (p009.lo) .lt,
  -- P010.normalization; P010: lambda=1/3, y=9/8: 1027527/10000000 < L_minus(1+(1/3)/(3080217/1000000)); L_plus(1+(1/3)/(30802167/10000000)) < 1027530/10000000.
  Comparison.ofRats ((0 : Rat)) (p010.lo) .lt,
  -- P011.normalization; P011: lambda=1/3, y=21/16: 859165/10000000 < L_minus(1+(1/3)/(37154509/10000000)); L_plus(1+(1/3)/(18577253/5000000)) < 859168/10000000.
  Comparison.ofRats ((0 : Rat)) (p011.lo) .lt,
  -- P012.normalization; P012: lambda=1/3, y=3/2: 717405/10000000 < L_minus(1+(1/3)/(22408447/5000000)); L_plus(1+(1/3)/(44816889/10000000)) < 717409/10000000.
  Comparison.ofRats ((0 : Rat)) (p012.lo) .lt,
  -- P013.normalization; P013: lambda=1/3, y=15/8: 498545/10000000 < L_minus(1+(1/3)/(32604103/5000000)); L_plus(1+(1/3)/(6520819/1000000)) < 498548/10000000.
  Comparison.ofRats ((0 : Rat)) (p013.lo) .lt,
  -- P014.normalization; P014: lambda=1/3, y=9/4: 345298/10000000 < L_minus(1+(1/3)/(23719357/2500000)); L_plus(1+(1/3)/(94877357/10000000)) < 345301/10000000.
  Comparison.ofRats ((0 : Rat)) (p014.lo) .lt,
  -- P015.normalization; P015: lambda=1/3, y=3: 164592/10000000 < L_minus(1+(1/3)/(100428229/5000000)); L_plus(1+(1/3)/(40171073/2000000)) < 164596/10000000.
  Comparison.ofRats ((0 : Rat)) (p015.lo) .lt,
  -- P016.normalization; P016: lambda=3/5, y=3/32: 4358687/10000000 < L_minus(1+(3/5)/(10982853/10000000)); L_plus(1+(3/5)/(219657/200000)) < 4358693/10000000.
  Comparison.ofRats ((0 : Rat)) (p016.lo) .lt,
  -- P017.normalization; P017: lambda=3/5, y=3/16: 4037416/10000000 < L_minus(1+(3/5)/(376947/312500)); L_plus(1+(3/5)/(12062301/10000000)) < 4037422/10000000.
  Comparison.ofRats ((0 : Rat)) (p017.lo) .lt,
  -- P018.normalization; P018: lambda=3/5, y=15/64: 3884129/10000000 < L_minus(1+(3/5)/(6320593/5000000)); L_plus(1+(3/5)/(12641183/10000000)) < 3884135/10000000.
  Comparison.ofRats ((0 : Rat)) (p018.lo) .lt,
  -- P019.normalization; P019: lambda=3/5, y=9/32: 3735638/10000000 < L_minus(1+(3/5)/(13247849/10000000)); L_plus(1+(3/5)/(6623923/5000000)) < 3735644/10000000.
  Comparison.ofRats ((0 : Rat)) (p019.lo) .lt,
  -- P020.normalization; P020: lambda=3/5, y=21/64: 3591861/10000000 < L_minus(1+(3/5)/(13883627/10000000)); L_plus(1+(3/5)/(1735453/1250000)) < 3591867/10000000.
  Comparison.ofRats ((0 : Rat)) (p020.lo) .lt,
  -- P021.normalization; P021: lambda=3/5, y=3/8: 3452713/10000000 < L_minus(1+(3/5)/(3637479/2500000)); L_plus(1+(3/5)/(14549913/10000000)) < 3452719/10000000.
  Comparison.ofRats ((0 : Rat)) (p021.lo) .lt,
  -- P022.normalization; P022: lambda=3/5, y=27/64: 3318108/10000000 < L_minus(1+(3/5)/(15248181/10000000)); L_plus(1+(3/5)/(7624089/5000000)) < 3318113/10000000.
  Comparison.ofRats ((0 : Rat)) (p022.lo) .lt,
  -- P023.normalization; P023: lambda=3/5, y=15/32: 3187955/10000000 < L_minus(1+(3/5)/(3994989/2500000)); L_plus(1+(3/5)/(15979953/10000000)) < 3187960/10000000.
  Comparison.ofRats ((0 : Rat)) (p023.lo) .lt,
  -- P024.normalization; P024: lambda=3/5, y=9/16: 2940636/10000000 < L_minus(1+(3/5)/(4387637/2500000)); L_plus(1+(3/5)/(3510109/2000000)) < 2940642/10000000.
  Comparison.ofRats ((0 : Rat)) (p024.lo) .lt,
  -- P025.normalization; P025: lambda=3/5, y=21/32: 2710003/10000000 < L_minus(1+(3/5)/(9637753/5000000)); L_plus(1+(3/5)/(19275503/10000000)) < 2710008/10000000.
  Comparison.ofRats ((0 : Rat)) (p025.lo) .lt,
  -- P026.normalization; P026: lambda=3/5, y=3/4: 2495280/10000000 < L_minus(1+(3/5)/(10585001/5000000)); L_plus(1+(3/5)/(21169999/10000000)) < 2495285/10000000.
  Comparison.ofRats ((0 : Rat)) (p026.lo) .lt,
  -- P027.normalization; P027: lambda=3/5, y=27/32: 2295680/10000000 < L_minus(1+(3/5)/(11625349/5000000)); L_plus(1+(3/5)/(4650139/2000000)) < 2295685/10000000.
  Comparison.ofRats ((0 : Rat)) (p027.lo) .lt,
  -- P028.normalization; P028: lambda=3/5, y=15/16: 2110411/10000000 < L_minus(1+(3/5)/(3191987/1250000)); L_plus(1+(3/5)/(25535893/10000000)) < 2110415/10000000.
  Comparison.ofRats ((0 : Rat)) (p028.lo) .lt,
  -- P029.normalization; P029: lambda=3/5, y=9/8: 1779715/10000000 < L_minus(1+(3/5)/(3080217/1000000)); L_plus(1+(3/5)/(30802167/10000000)) < 1779718/10000000.
  Comparison.ofRats ((0 : Rat)) (p029.lo) .lt,
  -- P030.normalization; P030: lambda=3/5, y=21/16: 1497016/10000000 < L_minus(1+(3/5)/(37154509/10000000)); L_plus(1+(3/5)/(18577253/5000000)) < 1497019/10000000.
  Comparison.ofRats ((0 : Rat)) (p030.lo) .lt,
  -- P031.normalization; P031: lambda=3/5, y=3/2: 1256435/10000000 < L_minus(1+(3/5)/(22408447/5000000)); L_plus(1+(3/5)/(44816889/10000000)) < 1256439/10000000.
  Comparison.ofRats ((0 : Rat)) (p031.lo) .lt,
  -- P032.normalization; P032: lambda=3/5, y=27/16: 1052503/10000000 < L_minus(1+(3/5)/(6757437/1250000)); L_plus(1+(3/5)/(1689359/312500)) < 1052506/10000000.
  Comparison.ofRats ((0 : Rat)) (p032.lo) .lt,
  -- P033.normalization; P033: lambda=3/5, y=15/8: 880226/10000000 < L_minus(1+(3/5)/(32604103/5000000)); L_plus(1+(3/5)/(6520819/1000000)) < 880229/10000000.
  Comparison.ofRats ((0 : Rat)) (p033.lo) .lt,
  -- P034.normalization; P034: lambda=3/5, y=9/4: 613202/10000000 < L_minus(1+(3/5)/(23719357/2500000)); L_plus(1+(3/5)/(94877357/10000000)) < 613206/10000000.
  Comparison.ofRats ((0 : Rat)) (p034.lo) .lt,
  -- P035.normalization; P035: lambda=3/5, y=3: 294344/10000000 < L_minus(1+(3/5)/(100428229/5000000)); L_plus(1+(3/5)/(40171073/2000000)) < 294349/10000000.
  Comparison.ofRats ((0 : Rat)) (p035.lo) .lt,
  -- P036.normalization; P036: lambda=7/8, y=3/16: 5454589/10000000 < L_minus(1+(7/8)/(376947/312500)); L_plus(1+(7/8)/(12062301/10000000)) < 5454595/10000000.
  Comparison.ofRats ((0 : Rat)) (p036.lo) .lt,
  -- P037.normalization; P037: lambda=7/8, y=9/32: 5071092/10000000 < L_minus(1+(7/8)/(13247849/10000000)); L_plus(1+(7/8)/(6623923/5000000)) < 5071098/10000000.
  Comparison.ofRats ((0 : Rat)) (p037.lo) .lt,
  -- P038.normalization; P038: lambda=7/8, y=21/64: 4887262/10000000 < L_minus(1+(7/8)/(13883627/10000000)); L_plus(1+(7/8)/(1735453/1250000)) < 4887268/10000000.
  Comparison.ofRats ((0 : Rat)) (p038.lo) .lt,
  -- P039.normalization; P039: lambda=7/8, y=3/8: 4708643/10000000 < L_minus(1+(7/8)/(3637479/2500000)); L_plus(1+(7/8)/(14549913/10000000)) < 4708649/10000000.
  Comparison.ofRats ((0 : Rat)) (p039.lo) .lt,
  -- P040.normalization; P040: lambda=7/8, y=27/64: 4535176/10000000 < L_minus(1+(7/8)/(15248181/10000000)); L_plus(1+(7/8)/(7624089/5000000)) < 4535181/10000000.
  Comparison.ofRats ((0 : Rat)) (p040.lo) .lt,
  -- P041.normalization; P041: lambda=7/8, y=15/32: 4366799/10000000 < L_minus(1+(7/8)/(3994989/2500000)); L_plus(1+(7/8)/(15979953/10000000)) < 4366804/10000000.
  Comparison.ofRats ((0 : Rat)) (p041.lo) .lt,
  -- P042.normalization; P042: lambda=7/8, y=33/64: 4203445/10000000 < L_minus(1+(7/8)/(334937/200000)); L_plus(1+(7/8)/(16746847/10000000)) < 4203450/10000000.
  Comparison.ofRats ((0 : Rat)) (p042.lo) .lt,
  -- P043.normalization; P043: lambda=7/8, y=9/16: 4045043/10000000 < L_minus(1+(7/8)/(4387637/2500000)); L_plus(1+(7/8)/(3510109/2000000)) < 4045049/10000000.
  Comparison.ofRats ((0 : Rat)) (p043.lo) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization003
