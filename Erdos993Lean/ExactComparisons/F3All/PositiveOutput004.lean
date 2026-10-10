module

public import Erdos993Lean.ExactComparisons.F3All.Data

/-! Generated from the F3 text of version 2.10 of the manuscript.
No Python certificate evaluation is used; the checks are done by the Lean kernel. -/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
namespace Erdos993Lean.ExactComparisons.F3All.PositiveOutput004

def records : List Comparison := [
  -- A062.positive_gp; A062: D=6/5, lambda in [28/25,263/200], y in [3/8,27/64], m=1/3: delta > 867865/1000000 > 0; B_balance > 35908/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((867865 : Rat)) .lt,
  -- A062.positive_g; A062: D=6/5, lambda in [28/25,263/200], y in [3/8,27/64], m=1/3: delta > 867865/1000000 > 0; B_balance > 35908/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((35908 : Rat)) .lt,
  -- A063.positive_gp; A063: D=6/5, lambda in [28/25,263/200], y in [27/64,15/32], m=2/5: delta > 847063/1000000 > 0; B_balance > 7362/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((847063 : Rat)) .lt,
  -- A063.positive_g; A063: D=6/5, lambda in [28/25,263/200], y in [27/64,15/32], m=2/5: delta > 847063/1000000 > 0; B_balance > 7362/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7362 : Rat)) .lt,
  -- A064.positive_gp; A064: D=6/5, lambda in [28/25,263/200], y in [15/32,63/128], m=2/5: delta > 846449/1000000 > 0; B_balance > 6242/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((846449 : Rat)) .lt,
  -- A064.positive_g; A064: D=6/5, lambda in [28/25,263/200], y in [15/32,63/128], m=2/5: delta > 846449/1000000 > 0; B_balance > 6242/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((6242 : Rat)) .lt,
  -- A065.positive_gp; A065: D=6/5, lambda in [28/25,263/200], y in [63/128,33/64], m=9/20: delta > 836195/1000000 > 0; B_balance > 1832/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((836195 : Rat)) .lt,
  -- A065.positive_g; A065: D=6/5, lambda in [28/25,263/200], y in [63/128,33/64], m=9/20: delta > 836195/1000000 > 0; B_balance > 1832/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1832 : Rat)) .lt,
  -- A066.positive_gp; A066: D=6/5, lambda in [28/25,263/200], y in [33/64,69/128], m=49/100: delta > 825927/1000000 > 0; B_balance > 258/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((825927 : Rat)) .lt,
  -- A066.positive_g; A066: D=6/5, lambda in [28/25,263/200], y in [33/64,69/128], m=49/100: delta > 825927/1000000 > 0; B_balance > 258/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((258 : Rat)) .lt,
  -- A067.positive_gp; A067: D=6/5, lambda in [28/25,263/200], y in [69/128,9/16], m=49/100: delta > 815653/1000000 > 0; B_balance > 1277/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((815653 : Rat)) .lt,
  -- A067.positive_g; A067: D=6/5, lambda in [28/25,263/200], y in [69/128,9/16], m=49/100: delta > 815653/1000000 > 0; B_balance > 1277/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((1277 : Rat)) .lt,
  -- A068.positive_gp; A068: D=6/5, lambda in [28/25,263/200], y in [9/16,75/128], m=49/100: delta > 805381/1000000 > 0; B_balance > 2398/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((805381 : Rat)) .lt,
  -- A068.positive_g; A068: D=6/5, lambda in [28/25,263/200], y in [9/16,75/128], m=49/100: delta > 805381/1000000 > 0; B_balance > 2398/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2398 : Rat)) .lt,
  -- A069.positive_gp; A069: D=6/5, lambda in [28/25,263/200], y in [75/128,39/64], m=49/100: delta > 795121/1000000 > 0; B_balance > 3620/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((795121 : Rat)) .lt,
  -- A069.positive_g; A069: D=6/5, lambda in [28/25,263/200], y in [75/128,39/64], m=49/100: delta > 795121/1000000 > 0; B_balance > 3620/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((3620 : Rat)) .lt,
  -- A070.positive_gp; A070: D=6/5, lambda in [28/25,263/200], y in [39/64,81/128], m=49/100: delta > 784881/1000000 > 0; B_balance > 4942/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((784881 : Rat)) .lt,
  -- A070.positive_g; A070: D=6/5, lambda in [28/25,263/200], y in [39/64,81/128], m=49/100: delta > 784881/1000000 > 0; B_balance > 4942/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((4942 : Rat)) .lt,
  -- A071.positive_gp; A071: D=6/5, lambda in [28/25,263/200], y in [81/128,21/32], m=49/100: delta > 774673/1000000 > 0; B_balance > 6364/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((774673 : Rat)) .lt,
  -- A071.positive_g; A071: D=6/5, lambda in [28/25,263/200], y in [81/128,21/32], m=49/100: delta > 774673/1000000 > 0; B_balance > 6364/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((6364 : Rat)) .lt,
  -- A072.positive_gp; A072: D=6/5, lambda in [28/25,263/200], y in [21/32,87/128], m=49/100: delta > 764504/1000000 > 0; B_balance > 7886/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((764504 : Rat)) .lt,
  -- A072.positive_g; A072: D=6/5, lambda in [28/25,263/200], y in [21/32,87/128], m=49/100: delta > 764504/1000000 > 0; B_balance > 7886/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((7886 : Rat)) .lt,
  -- A073.positive_gp; A073: D=6/5, lambda in [28/25,263/200], y in [87/128,45/64], m=49/100: delta > 754385/1000000 > 0; B_balance > 9506/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((754385 : Rat)) .lt,
  -- A073.positive_g; A073: D=6/5, lambda in [28/25,263/200], y in [87/128,45/64], m=49/100: delta > 754385/1000000 > 0; B_balance > 9506/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((9506 : Rat)) .lt,
  -- A074.positive_gp; A074: D=6/5, lambda in [28/25,263/200], y in [45/64,93/128], m=49/100: delta > 744327/1000000 > 0; B_balance > 11227/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((744327 : Rat)) .lt,
  -- A074.positive_g; A074: D=6/5, lambda in [28/25,263/200], y in [45/64,93/128], m=49/100: delta > 744327/1000000 > 0; B_balance > 11227/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((11227 : Rat)) .lt,
  -- A075.positive_gp; A075: D=6/5, lambda in [28/25,263/200], y in [93/128,3/4], m=49/100: delta > 734338/1000000 > 0; B_balance > 13050/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((734338 : Rat)) .lt,
  -- A075.positive_g; A075: D=6/5, lambda in [28/25,263/200], y in [93/128,3/4], m=49/100: delta > 734338/1000000 > 0; B_balance > 13050/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13050 : Rat)) .lt,
  -- A076.positive_gp; A076: D=6/5, lambda in [28/25,263/200], y in [3/4,99/128], m=49/100: delta > 724432/1000000 > 0; B_balance > 15186/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((724432 : Rat)) .lt,
  -- A076.positive_g; A076: D=6/5, lambda in [28/25,263/200], y in [3/4,99/128], m=49/100: delta > 724432/1000000 > 0; B_balance > 15186/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((15186 : Rat)) .lt,
  -- A077.positive_gp; A077: D=6/5, lambda in [28/25,263/200], y in [99/128,51/64], m=49/100: delta > 714617/1000000 > 0; B_balance > 17444/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((714617 : Rat)) .lt,
  -- A077.positive_g; A077: D=6/5, lambda in [28/25,263/200], y in [99/128,51/64], m=49/100: delta > 714617/1000000 > 0; B_balance > 17444/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((17444 : Rat)) .lt,
  -- A078.positive_gp; A078: D=6/5, lambda in [28/25,263/200], y in [51/64,105/128], m=49/100: delta > 704905/1000000 > 0; B_balance > 19816/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((704905 : Rat)) .lt,
  -- A078.positive_g; A078: D=6/5, lambda in [28/25,263/200], y in [51/64,105/128], m=49/100: delta > 704905/1000000 > 0; B_balance > 19816/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((19816 : Rat)) .lt,
  -- A079.positive_gp; A079: D=6/5, lambda in [28/25,263/200], y in [105/128,27/32], m=49/100: delta > 695307/1000000 > 0; B_balance > 22310/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((695307 : Rat)) .lt,
  -- A079.positive_g; A079: D=6/5, lambda in [28/25,263/200], y in [105/128,27/32], m=49/100: delta > 695307/1000000 > 0; B_balance > 22310/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((22310 : Rat)) .lt,
  -- A080.positive_gp; A080: D=6/5, lambda in [28/25,263/200], y in [27/32,111/128], m=49/100: delta > 685835/1000000 > 0; B_balance > 24900/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((685835 : Rat)) .lt,
  -- A080.positive_g; A080: D=6/5, lambda in [28/25,263/200], y in [27/32,111/128], m=49/100: delta > 685835/1000000 > 0; B_balance > 24900/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((24900 : Rat)) .lt,
  -- A081.positive_gp; A081: D=6/5, lambda in [28/25,263/200], y in [111/128,57/64], m=49/100: delta > 676502/1000000 > 0; B_balance > 27607/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((676502 : Rat)) .lt,
  -- A081.positive_g; A081: D=6/5, lambda in [28/25,263/200], y in [111/128,57/64], m=49/100: delta > 676502/1000000 > 0; B_balance > 27607/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((27607 : Rat)) .lt,
  -- A082.positive_gp; A082: D=6/5, lambda in [28/25,263/200], y in [57/64,15/16], m=49/100: delta > 642926/1000000 > 0; B_balance > 180/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((642926 : Rat)) .lt,
  -- A082.positive_g; A082: D=6/5, lambda in [28/25,263/200], y in [57/64,15/16], m=49/100: delta > 642926/1000000 > 0; B_balance > 180/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((180 : Rat)) .lt,
  -- A083.positive_gp; A083: D=6/5, lambda in [28/25,263/200], y in [15/16,63/64], m=49/100: delta > 624679/1000000 > 0; B_balance > 2458/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((624679 : Rat)) .lt,
  -- A083.positive_g; A083: D=6/5, lambda in [28/25,263/200], y in [15/16,63/64], m=49/100: delta > 624679/1000000 > 0; B_balance > 2458/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((2458 : Rat)) .lt,
  -- A084.positive_gp; A084: D=6/5, lambda in [28/25,263/200], y in [63/64,33/32], m=49/100: delta > 607196/1000000 > 0; B_balance > 5226/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((607196 : Rat)) .lt,
  -- A084.positive_g; A084: D=6/5, lambda in [28/25,263/200], y in [63/64,33/32], m=49/100: delta > 607196/1000000 > 0; B_balance > 5226/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((5226 : Rat)) .lt,
  -- A085.positive_gp; A085: D=6/5, lambda in [28/25,263/200], y in [33/32,69/64], m=49/100: delta > 590581/1000000 > 0; B_balance > 8736/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((590581 : Rat)) .lt,
  -- A085.positive_g; A085: D=6/5, lambda in [28/25,263/200], y in [33/32,69/64], m=49/100: delta > 590581/1000000 > 0; B_balance > 8736/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((8736 : Rat)) .lt,
  -- A086.positive_gp; A086: D=6/5, lambda in [28/25,263/200], y in [69/64,9/8], m=49/100: delta > 574942/1000000 > 0; B_balance > 13342/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((574942 : Rat)) .lt,
  -- A086.positive_g; A086: D=6/5, lambda in [28/25,263/200], y in [69/64,9/8], m=49/100: delta > 574942/1000000 > 0; B_balance > 13342/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((13342 : Rat)) .lt,
  -- A087.positive_gp; A087: D=6/5, lambda in [28/25,263/200], y in [9/8,75/64], m=49/100: delta > 560391/1000000 > 0; B_balance > 19524/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((560391 : Rat)) .lt,
  -- A087.positive_g; A087: D=6/5, lambda in [28/25,263/200], y in [9/8,75/64], m=49/100: delta > 560391/1000000 > 0; B_balance > 19524/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((19524 : Rat)) .lt,
  -- A088.positive_gp; A088: D=6/5, lambda in [28/25,263/200], y in [75/64,39/32], m=49/100: delta > 547042/1000000 > 0; B_balance > 27918/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((547042 : Rat)) .lt,
  -- A088.positive_g; A088: D=6/5, lambda in [28/25,263/200], y in [75/64,39/32], m=49/100: delta > 547042/1000000 > 0; B_balance > 27918/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((27918 : Rat)) .lt,
  -- A089.positive_gp; A089: D=6/5, lambda in [28/25,263/200], y in [39/32,81/64], m=49/100: delta > 534056/1000000 > 0; B_balance > 35070/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((534056 : Rat)) .lt,
  -- A089.positive_g; A089: D=6/5, lambda in [28/25,263/200], y in [39/32,81/64], m=49/100: delta > 534056/1000000 > 0; B_balance > 35070/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((35070 : Rat)) .lt,
  -- A090.positive_gp; A090: D=6/5, lambda in [28/25,263/200], y in [81/64,21/16], m=49/100: delta > 522235/1000000 > 0; B_balance > 44319/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((522235 : Rat)) .lt,
  -- A090.positive_g; A090: D=6/5, lambda in [28/25,263/200], y in [81/64,21/16], m=49/100: delta > 522235/1000000 > 0; B_balance > 44319/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((44319 : Rat)) .lt,
  -- A091.positive_gp; A091: D=6/5, lambda in [28/25,263/200], y in [21/16,87/64], m=49/100: delta > 511897/1000000 > 0; B_balance > 57594/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((511897 : Rat)) .lt,
  -- A091.positive_g; A091: D=6/5, lambda in [28/25,263/200], y in [21/16,87/64], m=49/100: delta > 511897/1000000 > 0; B_balance > 57594/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((57594 : Rat)) .lt,
  -- A092.positive_gp; A092: D=6/5, lambda in [28/25,263/200], y in [87/64,45/32], m=49/100: delta > 503176/1000000 > 0; B_balance > 76301/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((503176 : Rat)) .lt,
  -- A092.positive_g; A092: D=6/5, lambda in [28/25,263/200], y in [87/64,45/32], m=49/100: delta > 503176/1000000 > 0; B_balance > 76301/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((76301 : Rat)) .lt,
  -- A093.positive_gp; A093: D=6/5, lambda in [28/25,263/200], y in [45/32,93/64], m=49/100: delta > 496208/1000000 > 0; B_balance > 102115/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((496208 : Rat)) .lt,
  -- A093.positive_g; A093: D=6/5, lambda in [28/25,263/200], y in [45/32,93/64], m=49/100: delta > 496208/1000000 > 0; B_balance > 102115/1000000 > 0.
  Comparison.ofRats ((0 : Rat)) ((102115 : Rat)) .lt
]

theorem checked : check records = true := by decide +kernel
theorem sound : ∀ c ∈ records, c.rationalHolds := check_sound records checked
theorem record_count : records.length = 64 := by decide +kernel

end Erdos993Lean.ExactComparisons.F3All.PositiveOutput004
