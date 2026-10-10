module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.Normalization002

def records : List Comparison := [
  -- E065.normalization; E065: 22712093/10000000 < E_minus(105/128); E_plus(105/128) < 22712096/10000000.
  Comparison.ofRats ((1 : Rat)) (e065.lo) .le,
  -- E066.normalization; E066: 22818806/10000000 < E_minus(33/40); E_plus(33/40) < 22818809/10000000.
  Comparison.ofRats ((1 : Rat)) (e066.lo) .le,
  -- E067.normalization; E067: 22904537/10000000 < E_minus(663/800); E_plus(663/800) < 22904540/10000000.
  Comparison.ofRats ((1 : Rat)) (e067.lo) .le,
  -- E068.normalization; E068: 22976226/10000000 < E_minus(1331/1600); E_plus(1331/1600) < 22976229/10000000.
  Comparison.ofRats ((1 : Rat)) (e068.lo) .le,
  -- E069.normalization; E069: 22979816/10000000 < E_minus(213/256); E_plus(213/256) < 22979819/10000000.
  Comparison.ofRats ((1 : Rat)) (e069.lo) .le,
  -- E070.normalization; E070: 23163668/10000000 < E_minus(21/25); E_plus(21/25) < 23163671/10000000.
  Comparison.ofRats ((1 : Rat)) (e070.lo) .le,
  -- E071.normalization; E071: 23250695/10000000 < E_minus(27/32); E_plus(27/32) < 23250698/10000000.
  Comparison.ofRats ((1 : Rat)) (e071.lo) .le,
  -- E072.normalization; E072: 23414753/10000000 < E_minus(1089/1280); E_plus(1089/1280) < 23414756/10000000.
  Comparison.ofRats ((1 : Rat)) (e072.lo) .le,
  -- E073.normalization; E073: 23524767/10000000 < E_minus(219/256); E_plus(219/256) < 23524770/10000000.
  Comparison.ofRats ((1 : Rat)) (e073.lo) .le,
  -- E074.normalization; E074: 23616840/10000000 < E_minus(55/64); E_plus(55/64) < 23616843/10000000.
  Comparison.ofRats ((1 : Rat)) (e074.lo) .le,
  -- E075.normalization; E075: 23637145/10000000 < E_minus(11011/12800); E_plus(11011/12800) < 23637148/10000000.
  Comparison.ofRats ((1 : Rat)) (e075.lo) .le,
  -- E076.normalization; E076: 23802069/10000000 < E_minus(111/128); E_plus(111/128) < 23802073/10000000.
  Comparison.ofRats ((1 : Rat)) (e076.lo) .le,
  -- E077.normalization; E077: 23861649/10000000 < E_minus(2783/3200); E_plus(2783/3200) < 23861652/10000000.
  Comparison.ofRats ((1 : Rat)) (e077.lo) .le,
  -- E078.normalization; E078: 24082641/10000000 < E_minus(225/256); E_plus(225/256) < 24082644/10000000.
  Comparison.ofRats ((1 : Rat)) (e078.lo) .le,
  -- E079.normalization; E079: 24088286/10000000 < E_minus(11253/12800); E_plus(11253/12800) < 24088289/10000000.
  Comparison.ofRats ((1 : Rat)) (e079.lo) .le,
  -- E080.normalization; E080: 24317075/10000000 < E_minus(5687/6400); E_plus(5687/6400) < 24317078/10000000.
  Comparison.ofRats ((1 : Rat)) (e080.lo) .le,
  -- E081.normalization; E081: 24366519/10000000 < E_minus(57/64); E_plus(57/64) < 24366522/10000000.
  Comparison.ofRats ((1 : Rat)) (e081.lo) .le,
  -- E082.normalization; E082: 24412249/10000000 < E_minus(357/400); E_plus(357/400) < 24412252/10000000.
  Comparison.ofRats ((1 : Rat)) (e082.lo) .le,
  -- E083.normalization; E083: 24442784/10000000 < E_minus(143/160); E_plus(143/160) < 24442787/10000000.
  Comparison.ofRats ((1 : Rat)) (e083.lo) .le,
  -- E084.normalization; E084: 24781193/10000000 < E_minus(363/400); E_plus(363/400) < 24781196/10000000.
  Comparison.ofRats ((1 : Rat)) (e084.lo) .le,
  -- E085.normalization; E085: 24944355/10000000 < E_minus(117/128); E_plus(117/128) < 24944358/10000000.
  Comparison.ofRats ((1 : Rat)) (e085.lo) .le,
  -- E086.normalization; E086: 25092902/10000000 < E_minus(23/25); E_plus(23/25) < 25092905/10000000.
  Comparison.ofRats ((1 : Rat)) (e086.lo) .le,
  -- E087.normalization; E087: 25254170/10000000 < E_minus(5929/6400); E_plus(5929/6400) < 25254173/10000000.
  Comparison.ofRats ((1 : Rat)) (e087.lo) .le,
  -- E088.normalization; E088: 25535893/10000000 < E_minus(15/16); E_plus(15/16) < 25535896/10000000.
  Comparison.ofRats ((1 : Rat)) (e088.lo) .le,
  -- E089.normalization; E089: 25736174/10000000 < E_minus(121/128); E_plus(121/128) < 25736177/10000000.
  Comparison.ofRats ((1 : Rat)) (e089.lo) .le,
  -- E090.normalization; E090: 26141459/10000000 < E_minus(123/128); E_plus(123/128) < 26141462/10000000.
  Comparison.ofRats ((1 : Rat)) (e090.lo) .le,
  -- E091.normalization; E091: 26182337/10000000 < E_minus(77/80); E_plus(77/80) < 26182340/10000000.
  Comparison.ofRats ((1 : Rat)) (e091.lo) .le,
  -- E092.normalization; E092: 26727955/10000000 < E_minus(1573/1600); E_plus(1573/1600) < 26727958/10000000.
  Comparison.ofRats ((1 : Rat)) (e092.lo) .le,
  -- E093.normalization; E093: 26761386/10000000 < E_minus(63/64); E_plus(63/64) < 26761389/10000000.
  Comparison.ofRats ((1 : Rat)) (e093.lo) .le,
  -- E094.normalization; E094: 27396014/10000000 < E_minus(129/128); E_plus(129/128) < 27396017/10000000.
  Comparison.ofRats ((1 : Rat)) (e094.lo) .le,
  -- E095.normalization; E095: 27731946/10000000 < E_minus(51/50); E_plus(51/50) < 27731949/10000000.
  Comparison.ofRats ((1 : Rat)) (e095.lo) .le,
  -- E096.normalization; E096: 27757957/10000000 < E_minus(3267/3200); E_plus(3267/3200) < 27757960/10000000.
  Comparison.ofRats ((1 : Rat)) (e096.lo) .le,
  -- E097.normalization; E097: 28045692/10000000 < E_minus(33/32); E_plus(33/32) < 28045695/10000000.
  Comparison.ofRats ((1 : Rat)) (e097.lo) .le,
  -- E098.normalization; E098: 28710777/10000000 < E_minus(135/128); E_plus(135/128) < 28710780/10000000.
  Comparison.ofRats ((1 : Rat)) (e098.lo) .le,
  -- E099.normalization; E099: 28827651/10000000 < E_minus(847/800); E_plus(847/800) < 28827654/10000000.
  Comparison.ofRats ((1 : Rat)) (e099.lo) .le,
  -- E100.normalization; E100: 29391633/10000000 < E_minus(69/64); E_plus(69/64) < 29391636/10000000.
  Comparison.ofRats ((1 : Rat)) (e100.lo) .le,
  -- E101.normalization; E101: 30041659/10000000 < E_minus(11/10); E_plus(11/10) < 30041662/10000000.
  Comparison.ofRats ((1 : Rat)) (e101.lo) .le,
  -- E102.normalization; E102: 30088636/10000000 < E_minus(141/128); E_plus(141/128) < 30088639/10000000.
  Comparison.ofRats ((1 : Rat)) (e102.lo) .le,
  -- E103.normalization; E103: 30802167/10000000 < E_minus(9/8); E_plus(9/8) < 30802170/10000000.
  Comparison.ofRats ((1 : Rat)) (e103.lo) .le,
  -- E104.normalization; E104: 31532619/10000000 < E_minus(147/128); E_plus(147/128) < 31532623/10000000.
  Comparison.ofRats ((1 : Rat)) (e104.lo) .le,
  -- E105.normalization; E105: 32280394/10000000 < E_minus(75/64); E_plus(75/64) < 32280397/10000000.
  Comparison.ofRats ((1 : Rat)) (e105.lo) .le,
  -- E106.normalization; E106: 33045901/10000000 < E_minus(153/128); E_plus(153/128) < 33045905/10000000.
  Comparison.ofRats ((1 : Rat)) (e106.lo) .le,
  -- E107.normalization; E107: 33534845/10000000 < E_minus(121/100); E_plus(121/100) < 33534848/10000000.
  Comparison.ofRats ((1 : Rat)) (e107.lo) .le,
  -- E108.normalization; E108: 33829562/10000000 < E_minus(39/32); E_plus(39/32) < 33829566/10000000.
  Comparison.ofRats ((1 : Rat)) (e108.lo) .le,
  -- E109.normalization; E109: 34631807/10000000 < E_minus(159/128); E_plus(159/128) < 34631811/10000000.
  Comparison.ofRats ((1 : Rat)) (e109.lo) .le,
  -- E110.normalization; E110: 35453077/10000000 < E_minus(81/64); E_plus(81/64) < 35453081/10000000.
  Comparison.ofRats ((1 : Rat)) (e110.lo) .le,
  -- E111.normalization; E111: 36293823/10000000 < E_minus(165/128); E_plus(165/128) < 36293826/10000000.
  Comparison.ofRats ((1 : Rat)) (e111.lo) .le,
  -- E112.normalization; E112: 37154506/10000000 < E_minus(21/16); E_plus(21/16) < 37154509/10000000.
  Comparison.ofRats ((1 : Rat)) (e112.lo) .le,
  -- E113.normalization; E113: 38035600/10000000 < E_minus(171/128); E_plus(171/128) < 38035603/10000000.
  Comparison.ofRats ((1 : Rat)) (e113.lo) .le,
  -- E114.normalization; E114: 38937588/10000000 < E_minus(87/64); E_plus(87/64) < 38937592/10000000.
  Comparison.ofRats ((1 : Rat)) (e114.lo) .le,
  -- E115.normalization; E115: 39860966/10000000 < E_minus(177/128); E_plus(177/128) < 39860970/10000000.
  Comparison.ofRats ((1 : Rat)) (e115.lo) .le,
  -- E116.normalization; E116: 40806242/10000000 < E_minus(45/32); E_plus(45/32) < 40806246/10000000.
  Comparison.ofRats ((1 : Rat)) (e116.lo) .le,
  -- E117.normalization; E117: 41773934/10000000 < E_minus(183/128); E_plus(183/128) < 41773938/10000000.
  Comparison.ofRats ((1 : Rat)) (e117.lo) .le,
  -- E118.normalization; E118: 42764574/10000000 < E_minus(93/64); E_plus(93/64) < 42764579/10000000.
  Comparison.ofRats ((1 : Rat)) (e118.lo) .le,
  -- E119.normalization; E119: 43778707/10000000 < E_minus(189/128); E_plus(189/128) < 43778712/10000000.
  Comparison.ofRats ((1 : Rat)) (e119.lo) .le,
  -- E120.normalization; E120: 44816889/10000000 < E_minus(3/2); E_plus(3/2) < 44816894/10000000.
  Comparison.ofRats ((1 : Rat)) (e120.lo) .le,
  -- E121.normalization; E121: 45879691/10000000 < E_minus(195/128); E_plus(195/128) < 45879696/10000000.
  Comparison.ofRats ((1 : Rat)) (e121.lo) .le,
  -- E122.normalization; E122: 46967697/10000000 < E_minus(99/64); E_plus(99/64) < 46967702/10000000.
  Comparison.ofRats ((1 : Rat)) (e122.lo) .le,
  -- E123.normalization; E123: 48081504/10000000 < E_minus(201/128); E_plus(201/128) < 48081509/10000000.
  Comparison.ofRats ((1 : Rat)) (e123.lo) .le,
  -- E124.normalization; E124: 49221724/10000000 < E_minus(51/32); E_plus(51/32) < 49221730/10000000.
  Comparison.ofRats ((1 : Rat)) (e124.lo) .le,
  -- E125.normalization; E125: 51583923/10000000 < E_minus(105/64); E_plus(105/64) < 51583931/10000000.
  Comparison.ofRats ((1 : Rat)) (e125.lo) .le,
  -- E126.normalization; E126: 54059488/10000000 < E_minus(27/16); E_plus(27/16) < 54059496/10000000.
  Comparison.ofRats ((1 : Rat)) (e126.lo) .le,
  -- E127.normalization; E127: 56653857/10000000 < E_minus(111/64); E_plus(111/64) < 56653866/10000000.
  Comparison.ofRats ((1 : Rat)) (e127.lo) .le,
  -- E128.normalization; E128: 59372732/10000000 < E_minus(57/32); E_plus(57/32) < 59372743/10000000.
  Comparison.ofRats ((1 : Rat)) (e128.lo) .le
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.Normalization002
